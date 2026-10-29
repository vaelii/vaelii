;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.serve
  "Headless EDN-over-HTTP daemon: one JVM owns one KB and serves it to remote clients
  (`vaelii.host.client`).  A thin reitit-ring + jetty layer over `vaelii.core`, the
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
  (`vaelii.host.subscribe`, docs/feed.md).  A `:poll` that waits runs **outside** the
  monitor; everything else about them is an ordinary EDN op.

  **One shared bearer token authenticates the caller.**  With `VAELII_API_TOKEN` set
  (`guard/api-token`), every request presents `Authorization: Bearer <token>` or is
  answered 401 with a `WWW-Authenticate: Bearer` challenge; `GET /health` is the one
  route that answers without it.  One token for the process, not a session and not an
  identity — per-caller identity is a reverse proxy's job, and this is the check that
  has to exist below it.  Binding anything but loopback **requires** a token (`-main`
  refuses to start otherwise); on the loopback default it is optional, and a daemon
  without one is drivable by every process on the machine.

  **A per-principal token table replaces the shared token** when `VAELII_TOKEN_TABLE`
  names one (`guard/token-table`): each token carries a grant naming a principal and the
  contexts it writes, and a write op lands only there, recorded under that principal
  (`bound-write`).  Reads stay open to every token in the table.

  `vaelii.host.guard` covers what a token does not, and matters most on the open
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
            [vaelii.host.guard :as guard]
            [vaelii.host.starter :as starter]
            [vaelii.host.subscribe :as sub]
            [vaelii.impl.assert-entry :as entry]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.config :as config]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.util.concurrent ExecutionException]
           [org.eclipse.jetty.server Server ServerConnector]
           [org.eclipse.jetty.util.component LifeCycle$Listener]))

;; ---- the op table: the allowlisted vaelii.core surface -------------------
;; op keyword -> (fn [kb args-vector]).  `apply`ing keeps the varying arities
;; (assert's optional context/opts, why-not's two shapes) working unchanged: the
;; client sends exactly the args it would pass in-process, minus the KB.

(defn- op [f] (fn [kb args] (apply f kb args)))

(defn- op*
  "The same, for a `vaelii.core` fn that takes **no KB** — the static key sets and the
  pure renderers (`levels`, `calculi`, `readable-sentence`, `sentence-of`,
  `quality-report`).  The
  daemon still supplies a KB to every row, so this one drops it; `kbless-ops` below is
  the list a caller generating from this table reads, since a closure cannot be asked
  which shape it has."
  [f] (fn [_kb args] (apply f args)))

(def kbless-ops
  "The ops whose `vaelii.core` fn takes no KB (`op*` above).  Held as data rather than
  left implicit in the closures, because a generator reading this table has to know
  whether an op's first `vaelii.core` parameter is the KB the daemon supplies or an
  argument the caller sends: `vaelii.host.client`'s wrappers (arity for arity) read it
  here, and so does any caller that builds a call schema from `ops`."
  #{:levels :calculi :readable-sentence :sentence-of :quality-report})

(defn- wire-handles
  "`core/handles` as a sorted vector.  The whole-KB handle set is a `java.util.Set` that is
  deliberately *not* an `IPersistentSet` at scale (`vaelii.impl.handle-set`), and such a
  value has no EDN print form — it would reach a client as `#object[…]`.  Sorted, so two
  daemons over the same store answer the same bytes."
  [kb] (vec (sort (v/handles kb))))

(defn- without-resume
  "Wrap an anytime read (`ask-within` / `prove-within`) so its partial result crosses the
  wire.  The contract's `:resume` is a **function** closing over an unrealized lazy tail
  or a DFS goal stack, and neither a function nor the heap it retains crosses an EDN wire —
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
  is not the caller's alone: every other request queues behind it.  The clock ceiling,
  `:max-ms` (`config/max-query-ms`), bounds that cost at every entry point that takes a
  clock, and such a row names no depth: a depth ceiling there would refuse a complete
  answer the clock already bounds.  `:query`, `:query?`, `:query-status` and `:argue` take
  no clock (`query-opt-keys` has no `:max-ms`), so the depth ceiling, `:max-depth`
  (`config/max-query-depth`), is their bound.  An anytime budget map is `:max-ms` and takes
  no default of its own.

  **The table holds the search bounds of reads, and no write's bound.** A read with no
  dial of its own is not on it: `:sentexes-matching` has nothing to raise, so there is
  nothing to clamp. The four backward-search entry points do have one
  (`core/ask-opt-keys`, `core/prove-opt-keys`), and are held to the clock ceiling.

  **Eight writes name a bound this table does not hold.** `:assert`, `:try-assert`,
  `:assert-many`, `:assert-rule` and `:forward-chain` read `:max-depth`, `:max-term-depth`
  and `:max-derivations` (`core/assert-opt-keys`, `forward-chain`'s accepted keys), and
  `:edit`, `:edit-with-consequences` and `:preview` read the same three keys off each batch
  entry's opts. All three bound the chaining fixpoint (`chain/default-chain-opts`: a
  term-nesting bound of 8 and no other when the request names none), which runs on the
  same monitor for its whole length, and a request may name any of them at any size. Every
  one but `:forward-chain` and `:preview` also reads `:max-ms`, which `write-bounds` holds
  to the write ceiling. `:forward-chain` reads `:max-ms` and no ceiling fills it in;
  `:preview` takes no clock. docs/operations.md states the same beside the ceilings."
  {:query              #{:max-depth}
   :query?             #{:max-depth}
   :query-status       #{:max-depth}
   :argue              #{:max-depth}
   :why-not            #{:max-ms}
   :search-tree        #{:max-ms}
   :compare-tacticians #{:max-ms}
   :ask                #{:max-ms}
   :ask?               #{:max-ms}
   :prove              #{:max-ms}
   :provable?          #{:max-ms}
   :ask-within         #{:max-ms}
   :prove-within       #{:max-ms}
   :kb-integrity       #{:max-ms :max-work :max-results}})

(def ^:private clock-fill
  "The ops whose ceiling has to reach a caller who sent **no option map at all**, and the
  arguments to fill in between what they sent and the map.

  A `:max-depth` op needs nothing here: absent there is a *smaller* question than the
  ceiling — no rule expansion at `query`'s entry point — so a call with no map is already
  inside the bound. Absent `:max-ms` is the opposite: it
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
  when the caller already sent one, or when the call is short of an argument `fill` has
  no default for (an arity refusal the op itself owes), else the tail of `fill` the call
  is short by, and then an empty map for `under-ceiling` to write the clock into."
  [args {:keys [fill option-arity]}]
  (let [first-fill (- option-arity 1 (count fill))]
    (cond
      (< (count args) first-fill) args
      (map? (peek args)) args
      (and (= option-arity (count args)) (nil? (peek args)))
      (assoc args (dec option-arity) {})
      :else
      (conj (into args (subvec fill (min (count fill) (- (count args) first-fill)))) {}))))

(defn- ceiling-for
  "The ceiling on `k`, or nil when the operator lifted it (`0`)."
  [k]
  (let [n (case k
            :max-ms    (config/max-query-ms)
            :max-depth (config/max-query-depth)
            :max-work    (config/integrity-max-work)
            :max-results (config/integrity-max-results))]
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
  no-rule-expansion answer at `query`'s entry point, a *smaller* question than the
  ceiling rather than a larger one."
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

  Wrapped **in the table** rather than at the HTTP route, because `POST /op` is not the
  only thing that dispatches through it: the browser's access facade does, and so can
  any in-process caller that generates calls from this map.  A ceiling applied at one
  entry point would be a ceiling the others do not have.

  For a `clock-fill` op the args are padded first, so a caller who sent no option map
  still gets one to be clamped: absent means *no clock* at every entry point, and no clock is
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

;; ---- the write ceiling: a clock a request may lower and not raise --------

(def write-bounds
  "The chaining writes the daemon holds to `config/max-write-ms`, and where each one's
  option map sits: `:option-arity` is the argument count that ends in the map, and `:fill`
  the `vaelii.core` defaults between the last argument a caller may send and the map.

  A chaining write runs on the daemon's single write monitor, so an operator may hold it
  to a clock as the reads `search-bounds` names are: a request may name a smaller
  `:max-ms` and is refused (`:over-ceiling`) for a larger one, and an absent one is the
  ceiling.  A write the clock ends is rolled back (docs/inference.md, \"Stopping a run\")."
  {:assert                 {:fill ['CxUniverse] :option-arity 3}
   :try-assert             {:fill ['CxUniverse] :option-arity 3}
   :assert-rule            {:fill ['CxUniverse] :option-arity 4}
   :assert-many            {:fill [] :option-arity 3}
   :edit                   {:fill [] :option-arity 2}
   :edit-with-consequences {:fill [] :option-arity 2}})

(defn- with-write-opts
  "`args` padded out to `option-arity` with `fill`'s defaults and an empty map, or as sent
  when the call is short of an argument `fill` has no default for or already names the
  map.  The map is told by position: `:edit`'s batch is a map too."
  [args {:keys [fill option-arity]}]
  (let [n          (count args)
        first-fill (- (long option-arity) 1 (count fill))]
    (cond
      (or (< n first-fill) (> n option-arity)) args
      (= n option-arity) (cond-> args (nil? (peek args)) (assoc (dec n) {}))
      :else              (conj (into args (subvec fill (- n first-fill))) {}))))

(defn- under-write-ceiling
  "`opts` with its `:max-ms` held under `ceiling`: refused (`:over-ceiling`) when larger,
  the ceiling when absent, as sent otherwise."
  [op ceiling opts]
  (let [v (:max-ms opts)]
    (cond
      (and (number? v) (> v ceiling))
      (throw (ex-info (str "op " op " :max-ms " v " is over this daemon's write ceiling of "
                           ceiling " — a request may name a smaller bound and not a larger"
                           " one, since a write holds the single writer for its whole run")
                      {:type :over-ceiling :op op :option :max-ms :requested v
                       :ceiling ceiling}))
      (nil? v) (assoc opts :max-ms ceiling)
      :else    opts)))

(defn- write-bounded
  "Wrap a chaining write's `(fn [kb args])` so its option map is held under
  `config/max-write-ms` (`write-bounds`) when the operator set one, or return `f` for any
  other op."
  [op f]
  (if-let [at (write-bounds op)]
    (fn [kb args]
      (let [ceiling (config/max-write-ms)]
        (if (pos? ceiling)
          (let [args (with-write-opts (vec args) at)]
            (f kb (if (= (count args) (:option-arity at))
                    (update args (dec (count args)) #(under-write-ceiling op ceiling %))
                    args)))
          (f kb args))))
    f))

(def ^:dynamic *served-kbs*
  "nil, or a fn from a string a request sends to the KB this server serves under that
  name, or nil when it serves none.  The browser binds it to its catalog around
  `handle-op` (`vaelii.browser.web/op-post`); the daemon serves one KB and leaves it nil."
  nil)

(defn- refuse-a-named-path!
  "Throw `:path-not-served` (403) for `op` unless `config/request-paths?`: a request picks
  among what the server serves and names no path on the server's host.  `verb` is
  \"read\" or \"write\", `why` says what the op takes and what the request named, and
  `what` is what the switch lets a request name."
  [op verb why what]
  (when-not (config/request-paths?)
    (throw (ex-info (str "a request names no path for this server to " verb ": "
                         (pr-str op) " " why ".  VAELII_REQUEST_PATHS=1 at the server's"
                         " start lets a request name " what " on the server's host.")
                    {:type :path-not-served :op op ::status 403}))))

(defn- served-side
  "The second side of a wire `:kb-diff`: the KB `*served-kbs*` names `b` for, or `b`
  itself when it is not a string.  A string naming no served KB is refused
  (`refuse-a-named-path!`) and nothing is read; under `VAELII_REQUEST_PATHS` it reaches
  `kb-diff`, which reads it as a text KB on the server's host."
  [b]
  (or (when-let [served (when (string? b) *served-kbs*)] (served b))
      (when (string? b)
        (refuse-a-named-path! :kb-diff "read"
                              (str "takes a KB this server serves, and " (pr-str b) " names none")
                              "a text KB"))
      b))

(defn- served-export!
  "`v/export!` to `dir`, refused (`refuse-a-named-path!`) before anything is written: the
  directory would be resolved on the server's host, and a request names none there."
  ([kb dir] (served-export! kb dir {}))
  ([kb dir opts]
   (refuse-a-named-path! :export "write"
                         (str "writes a dump to a directory on the server's host, and "
                              (pr-str dir) " names one")
                         "the directory")
   (v/export! kb dir opts)))

(def ops
  "The reachable operations, keyed by op keyword.  Reads, writes, and introspection —
  the working set a remote caller needs.  A `vaelii.core` fn that takes a KB is either a
  row here or a row of docs/operations.md's table of fns that are not ops, and the rule
  that page states decides which: data in and out, the KB rather than the process, a
  write through the checks every served write runs, and a cost a request can bound or one
  that grows with the KB.  `serve_parity_test` fails on a fn that is in neither.

  Every entry is wrapped by `bounded`, which is a no-op for an op `search-bounds` does
  not name, and by `write-bounded`, a no-op for an op `write-bounds` does not name."
  (into
   {}
   (map (fn [[op f]] [op (bounded op (write-bounded op f))]))
   {:assert       (op v/assert)
    :try-assert   (op v/try-assert)
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
    ;; asserting into is a dump of no single state.  The directory is a path on the
    ;; daemon's host, so it is refused unless `VAELII_REQUEST_PATHS` (`served-export!`)
    :export       (op served-export!)
    :preview      (op v/preview)
    :sentexes-matching (op v/sentexes-matching)
    :query        (op v/query)
    :query?       (op v/query?)
    ;; `query`'s answers with the report a bare `query` cannot give: whether the depth
    ;; bound cut the search.  The daemon's own ceiling is the depth a remote caller is
    ;; most likely to be cut by, so the read that says so is served under the same one
    :query-status (op v/query-status)
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
    :direct-genls (op v/direct-genls)
    :direct-specs (op v/direct-specs)
    :min-genls    (op v/min-genls)
    :max-specs    (op v/max-specs)
    ;; the common supertypes / subtypes of a collection of types, and the minimal / maximal
    ;; ones among them
    :common-genls     (op v/common-genls)
    :common-specs     (op v/common-specs)
    :min-common-genls (op v/min-common-genls)
    :max-common-specs (op v/max-common-specs)
    :min-context-parents  (op v/min-context-parents)
    :max-context-children (op v/max-context-children)
    :types        (op v/types)
    :relation?    (op v/relation?)
    :relation-arity (op v/relation-arity)
    :contexts     (op v/contexts)
    :sentex       (op v/sentex)
    :handle-of    (op v/handle-of)
    :find-sentexes (op v/find-sentexes)
    :find-sentexes-all (op v/find-sentexes-all)
    :defining-contexts (op v/defining-contexts)
    ;; the vocabulary — enumerate / count / search the terms themselves.  Served because
    ;; the alternative for a remote client is shipping every sentex over the wire to
    ;; collect the terms out of them.
    :terms        (op v/terms)
    :term-count   (op v/term-count)
    :sentex-count (op v/sentex-count)
    ;; the withheld-mint releases the daemon's open left undrawn, one count off the queue
    :owed-releases (op v/owed-releases)
    ;; the stored records the daemon's open found no premise and no justification for
    :unsupported  (op v/unsupported)
    :find-terms   (op v/find-terms)
    :forward-chain (op v/forward-chain)
    :chain-stats  (op v/chain-stats)
    ;; the per-rule breakdown behind chain-stats — what each forward rule placed, refused
    ;; (and why), or never did — read O(rules) off the ledger and the justification graph
    :chain-report (op v/chain-report)
    :conflicts    (op v/conflicts)
    ;; the question the edge solver was last asked — the contested assumptions and the
    ;; nogoods among them — beside `:conflicts`, the part of its answer it could not
    ;; satisfy.  A `Program` record, projected to a map like every other record
    :last-program (op v/last-program)
    :contradictions (op v/contradictions)
    :violations   (op v/violations)
    ;; the ledger alone, a deref, without the entries `violations` reads off the stored
    ;; firings and held sentexes
    :filed-violations (op v/filed-violations)
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
    :exists-violations        (op v/exists-violations)
    ;; the fluent-lane twin: per-instant clashes of a `functional_at_instant` function,
    ;; one declaration or every visible one.  Reported rather than filed, and a sweep
    ;; over every believed `time_point`, like the pair above (docs/time.md)
    :functional-at-instant-violations     (op v/functional-at-instant-violations)
    :all-functional-at-instant-violations (op v/all-functional-at-instant-violations)
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
    ;; a KB it does not own; safe to serve, and shared with vaelii.browser.access
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
    ;; the verdict a context reads on each justification of a handle: what a proof page
    ;; draws as supporting or not, which a remote reader cannot read off belief either
    :justification-verdicts    (op v/justification-verdicts)
    :lookup       (op v/lookup)
    :escalate     (op v/escalate)
    :explain-levels (op v/explain-levels)
    :count-in-context (op v/count-in-context)
    :sentexes-in-context   (op v/sentexes-in-context)
    :sentexes-with-arg     (op v/sentexes-with-arg)
    :sentexes-with-functor (op v/sentexes-with-functor)
    :sentexes-naming       (op v/sentexes-naming)
    :count-with-arg        (op v/count-with-arg)
    :count-with-functor    (op v/count-with-functor)
    :stored-first-args     (op v/stored-first-args)
    :disjoint-metatypes    (op v/disjoint-metatypes)
    :metatype-members      (op v/metatype-members)
    :separating-covers     (op v/separating-covers)
    :covers-of             (op v/covers-of)
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
    ;; the relationship between two types, read off the same closures as `:genl?` and
    ;; `:disjoint?` plus one facts-only read for a shared instance.  Each answers one pair
    ;; of types; the whole-hierarchy sweep behind `disjointness-audit` is not served
    ;; (docs/operations.md)
    :subsumption-status   (op v/subsumption-status)
    :subsumption-statuses (op v/subsumption-statuses)
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
    ;; the rest of `kbless-ops` (`:quality-report` above is the fifth): the retrieval
    ;; stack and the shipped calculi as data, and a stored rule's sentence — canonical, or
    ;; with its author's variable names put back.  A rule map crosses the wire with no
    ;; `:sentence`, so a client needs one of the last two to *display* a rule it fetched
    :levels            (op* v/levels)
    :calculi           (op* v/calculi)
    :readable-sentence (op* v/readable-sentence)
    :sentence-of       (op* v/sentence-of)
    ;; the three usability reads.  `:describe` is what a remote reader asks instead of a
    ;; dozen round trips — one call answers arity, declarations, properties, closures and
    ;; counts for a term, and the browser's term page is built on it.  `:why-not` is
    ;; already above and needs no entry of its own for `{:nearest n}`: the table `apply`s
    ;; the var, so a new arity crosses the wire the moment `vaelii.core` grows one
    :describe     (op v/describe)
    ;; `kb-diff`'s second side names a KB this server serves (`served-side`)
    :kb-diff      (op (fn [kb b] (v/kb-diff kb (served-side b))))}))

;; ---- the daemon's own ops: the change feed, held open with a cursor ------
;;
;; `ops` above is an allowlist of `vaelii.core` fns with the KB supplied, and the feed
;; cannot be one of them: `core/watch` takes a **function**, and a function does not
;; cross an EDN wire — the same wall `:export`'s `:on-progress` hits.  What crosses is
;; state with a cursor, which is state *this daemon* holds rather than anything the
;; engine has, so these three take the handler's subscription registry as well as its
;; KB (`vaelii.host.subscribe`, docs/feed.md).
;;
;; A second table rather than a second value shape in the first one, because the
;; difference is worth being able to state: `ops` is the surface a caller could also
;; reach in process, and `vaelii.browser.access` dispatches through it for exactly that
;; reason; `feed-ops` is the daemon's own, and a local caller holding a KB uses
;; `core/watch` instead.  A caller that generates calls from `ops` therefore cannot
;; allocate a subscription.

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

(defn- entry-arity-error?
  "Was ArityException `e` raised calling op `f`'s entry point, or a wrapper around it,
  with the caller's arguments?  The fn `e` names is then `f` or a fn `f` closes over,
  reached through at most six closures.  An arity error from a call inside the op names
  some other fn, and is a fault of the engine rather than of the request."
  [f ^clojure.lang.ArityException e]
  (let [thrower (.-name e)]
    (letfn [(reaches? [g depth]
              (and (instance? clojure.lang.Fn g)
                   (< depth 6)
                   (or (= thrower (.getName (class g)))
                       (boolean
                        (some (fn [^java.lang.reflect.Field fld]
                                (when-not (java.lang.reflect.Modifier/isStatic (.getModifiers fld))
                                  (.setAccessible fld true)
                                  (reaches? (.get fld g) (inc depth))))
                              (.getDeclaredFields (class g)))))))]
      (reaches? f 0))))

(defn- admit!
  "Call `admit` — nil, or a fn of no arguments that answers nil or a refusal
  `{:status :type :error}` — and throw the refusal.  Called inside the monitor, so the
  answer holds for the op that runs next.  The throw carries `::status`, which
  `handle-op` answers with in place of its own status for the `:type`."
  [admit]
  (when-let [{ty :type :keys [status error]} (when admit (admit))]
    (throw (ex-info error {:type ty ::status status}))))

(def feed-ops
  "The change-feed operations, keyed by op keyword — `(fn [ctx args])` over a `ctx` of
  `{:kb :registry :monitor}`, plus an optional `:admit`: `handle-op`'s, which `:watch`
  calls inside the monitor before it registers anything.

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
   (fn [{:keys [kb registry monitor] :as ctx} args]
     (let [[goal context] (feed-args! :watch args [[] '[goal context]])]
       (locking monitor
         (admit! (:admit ctx))
         (sub/watch registry kb goal context))))

   :poll
   (fn [{:keys [registry]} args]
     (let [[token cursor opts] (feed-args! :poll args ['[token cursor]
                                                       '[token cursor opts]])]
       (sub/poll registry token cursor opts)))

   :unwatch
   (fn [{:keys [registry monitor]} args]
     (let [[token] (feed-args! :unwatch args ['[token]])]
       (locking monitor (sub/unwatch registry token))))

   :watchers
   (fn [{:keys [registry]} args]
     (feed-args! :watchers args [[]])
     (sub/subscriptions registry))})

(def op-names
  "Every op keyword this daemon answers, sorted — the `vaelii.core` allowlist and the
  daemon's own together.  What an `:unknown-op` refusal hands back, so a caller
  discovering the surface sees one list rather than the larger half of two."
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
  born, and `wire_contract_test` asserts the pairing."
  #{:naming :not-well-formed :not-ground :not-range-restricted :not-indexable
    :disjunction-too-wide
    :shape :not-encodable
    :arg-type :inter-arg-type :arg-genl :quoted-arg-type :arg-position :arg-constraint-kind
    :arg-variable
    ;; the four relation-property refusals, which `check` reports and `assert` throws as
    ;; one family — a caller that asserts content a declared property forbids has made
    ;; one kind of mistake, so the four answer alike rather than splitting on which
    ;; property caught it
    :disjoint :functional :asymmetric :anti-transitive
    ;; `try-assert`'s refusal of a write that would open one of those clashes
    :definitional-clash
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
    :unknown-subscription :bad-cursor :too-many-subscriptions :too-many-waiters
    ;; a `{:keep? true}` abduction past the kept-context cap: the caller holds the
    ;; contexts and frees one with `:abduce-discard`, as with a subscription
    :too-many-kept
    ;; a write the caller's own bound ended, rolled back: the caller chose the bound and
    ;; decides whether to send the write again with a larger one
    :interrupted})

;; ---- the write boundary: what a token-table grant may write ---------------

(def write-ops
  "The ops that store, remove or annotate a sentex a request names, and `:export`, which
  writes the whole KB to the server's host: a token-table grant bounds them
  (`bound-write`).  The other ops read, store nothing (`:check`, `:check-edit`,
  `:preview`), or store what the request does not name: `:forward-chain` what the rules
  derive, `:abduce` its hypotheses in a scratch context (docs/operations.md, \"The token
  table\")."
  #{:assert :try-assert :assert-rule :assert-many :retract :edit :edit-with-consequences
    :add-provenance :export})

(defn- forbidden-context!
  "Throw `:forbidden-context` (403): `principal` may not write `context`, nil for a write
  no context bounds.  The message names the refused write as `what`, and says `why`."
  [op principal context what why]
  (throw (ex-info (str "op " (pr-str op) ": " principal " may not write " what " — " why)
                  {:type :forbidden-context :op op :principal principal :context context
                   ::status 403})))

(defn- check-claims!
  "Refuse `m` — a write's opts, its `:provenance` map or an `:add-provenance` map — when it
  names an identity `grant` does not hold (`:creator-mismatch`, 403): a `:principal`
  other than the grant's, and for a grant without `:admin?` a `:creator` other than its
  principal.  An admin grant names the creator of a write it makes for an agent.  Under
  no grant a named `:principal` is refused: the daemon records that key from a grant and
  never from a request."
  [op {:keys [principal admin?] :as grant} m]
  (doseq [k (if (and grant (not admin?)) [:creator :principal] [:principal])
          :when (and (map? m) (contains? m k) (not= principal (get m k)))]
    (throw (ex-info (str "op " (pr-str op) " names " k " " (pr-str (get m k))
                         (if grant
                           (str ", and the token it presents is " principal "'s")
                           (str ", which this server records from a token-table grant"
                                " and never from a request")))
                    {:type :creator-mismatch :op op :key k :claimed (get m k)
                     :principal principal ::status 403}))))

(defn- with-identity
  "`opts` — a write's option map, nil included — after `check-claims!` of it and of its
  `:provenance`, with the provenance `:principal` set to the grant's principal and
  `:creator` to it unless an admin grant named one.  Under no grant, `opts` as it came."
  [op {:keys [principal] :as grant} opts]
  (when-not (or (nil? opts) (map? opts))
    (throw (ex-info (str "op " (pr-str op) " takes an option map, got " (pr-str opts))
                    {:type :bad-args :op op})))
  (check-claims! op grant opts)
  (check-claims! op grant (:provenance opts))
  (if grant
    (-> opts
        (update :creator #(or % principal))
        (assoc :provenance (assoc (:provenance opts) :principal principal)))
    opts))

(def ^:private placement-declarations
  "The declarations that place every `(P …)` the KB holds, in any context, in CxUniverse:
  `forced_decontextualized_predicate` moves each there and `decontextualized_predicate`
  copies each there (docs/contexts.md)."
  '#{forced_decontextualized_predicate decontextualized_predicate})

(defn- apart
  "`lit` with every variable renamed to a primed spelling, which no stored rule's
  canonical variable (`?varN`) takes, so unifying the two binds neither's variable to the
  other's by name."
  [lit]
  (walk/postwalk #(if (sx/variable? %) (symbol (str % "'")) %) lit))

(defn- generators-on
  "The stored generators with an antecedent on one of the antecedent keys `ks`, as
  `[handle sentex]` pairs in content order.  Each key's antecedent posting is intersected
  with the `implies`-consequent posting before a record is decoded, so only a generator
  is.  Every stored generator is read, in whatever context it is stated, since a `genlCx`
  edge stored later would make it visible to the grant's context."
  [kb ks]
  (let [idx  (:index kb)
        gens (when (seq ks) (set (reads/as-stored-rules-by-consequent-global idx sx/rule-functor)))]
    (when (seq gens)
      (->> (into #{} (comp (mapcat #(reads/as-stored-rules-by-antecedent-global idx %))
                           (filter gens))
                 ks)
           (keep #(let [g (v/sentex kb %)] (when (rules/generator-sentex? g) [% g])))
           (nm/sort-by-content-key (fn [[_ g]] [(sx/sentence-of g) (:context g)]))))))

(defn- link-routes
  "The `[handle ctx]` supporter routes, read unscoped, by which a literal on `lo` reaches
  one on `hi` with its first two arguments exchanged under `swapped?`: `[[]]` for `lo`
  = `hi` read straight, each route no other covers over `genl` edges
  (`tax/general-reach-supports`), else the one route `tax/signed-reach-support` names
  across `genlInverse` edges, and `[[]]` when neither names one."
  [tax lo hi swapped?]
  (or (when-not swapped?
        (if (= lo hi) [[]] (not-empty (tax/general-reach-supports tax :genl lo hi nil))))
      (some-> (tax/signed-reach-support tax lo hi swapped? nil nil) vector)
      [[]]))

(defn- key-predicate
  "The predicate of antecedent key `k`: `k`, or the body's for a `[:not p]` key."
  [k]
  (if (vector? k) (second k) k))

(defn- parities
  "The parities `hi` is in the signed closure `[straight swapped]` with: false for
  straight, true for swapped (`tax/signed-closure`)."
  [[st sw] hi]
  (cond-> #{} (contains? st hi) (conj false) (contains? sw hi) (conj true)))

(defn- firing-contexts
  "The contexts a generator firing over a fact stated in `fc` is placed in, the fact
  reaching the antecedent over one of the `[handle ctx]` routes `routes`, in content
  order: `fc` when `fc` sees every context of some route, else per route the maximal
  common descendants of `fc` and the route's contexts.  This is the engine's placement
  (`chain/placements-over`) with the generator's own context left out, as
  `generators-on` reads every generator."
  [tax fc routes]
  (let [cs   (into #{} (mapcat #(tax/maximal-common-descendant-contexts tax (into [fc] (keep second) %)))
                   routes)
        base (filter cs (tax/maximal-common-descendant-contexts tax [fc]))]
    (nm/sort-by-content-key nm/name-key compare (if (seq base) base cs))))

(defn- placed-rules
  "The `[generator rule context]` triples for each of the `[handle sentex]` generators
  `gens` outside `seen` with an antecedent literal `lit`, stated in `fc`, matches: its
  handle, the rule it generates under that match's bindings, and each context of
  `(place fc routes)`.  `modes` maps an antecedent key to `{swapped? routes}`: the
  parities `lit` reaches it with, and the routes of each, as `place` reads them.  A
  swapped match reads `lit` with its first two arguments exchanged, as a fact reached
  over an odd number of `genlInverse` edges is read.  `lit` nil matches each antecedent
  `modes` keys with no binding."
  [gens modes lit fc seen place]
  (let [args #(if (vector? (rules/antecedent-key %)) (rest (second %)) (rest %))
        l    (when lit (args (apart lit)))]
    (for [[h g] gens
          :when (not (seen h))
          a (:antecedent g)
          [sw? rs] (sort-by first (modes (rules/antecedent-key a)))
          :when (or (nil? lit) (not sw?) (next l))
          b (if lit
              (some-> (res/unify-args (args a) (if sw? (list* (second l) (first l) (nnext l)) l))
                      vector)
              [res/no-bindings])
          c (place fc rs)]
      [h (res/substitute (rules/generated-rule (:consequent g)) b) c])))

(defn- generated-rules
  "The `[generator rule context]` triples storing literal `lit` in context `c` makes the
  engine write: a `defn*` fact's companion rules (`sx/defn-companion-rules`, generator
  nil) in `c`, and the `placed-rules` of each stored generator with an antecedent `lit`
  triggers (`rules/trigger-keys`), read through the signed closure of `lit`'s predicate."
  [kb lit c seen]
  (let [tax  (reasoning/taxonomy kb)
        ks   (set (rules/trigger-keys tax lit (:index kb)))
        k    (rules/antecedent-key lit)
        p    (key-predicate k)
        reach (tax/signed-closure tax (if (vector? k) :down :up) p nil)
        modes (fn [ak]
                (when (contains? ks ak)
                  (let [q (key-predicate ak)]
                    (into {} (map (fn [sw?] [sw? (if (vector? k) (link-routes tax q p sw?) (link-routes tax p q sw?))]))
                          (parities reach q)))))]
    (concat
     (when (sx/defn-sentence? lit) (map #(vector nil % c) (sx/defn-companion-rules lit)))
     (placed-rules (generators-on kb ks) modes lit c seen (partial firing-contexts tax)))))

(def ^:private edge-functors
  "The taxonomy edges `rules/trigger-keys` reads: storing `(genl Sub Super)` or
  `(genlInverse Sub Super)` makes a fact on a spec of Sub trigger an antecedent on a genl
  of Super."
  '#{genl genlInverse})

(defn- edge-generated-rules
  "The `[generator rule context]` triples storing the edge `(f sub super)` (`edge-functors`)
  in `context` makes the engine write: for each stored fact the edge connects to a stored
  generator's antecedent, each `placed-rules` triple that `generated-rules` reads of the
  fact once the edge is stored and did not read before it.  A positive fact on a spec `lo`
  of `sub` meets an antecedent on a genl `hi` of `super`; a negative fact on a genl `hi` of
  `super` meets a negated antecedent on a spec `lo` of `sub`.  A new route is a route from
  `lo` to `sub`, the edge in `context`, and a route from `super` to `hi`; the routes once
  the edge is stored are the new routes and the fact's stored ones that no other covers
  (`tax/uncovered`).  A variable `sub` or `super` may meet any fact, so each antecedent on
  a key the edge could reach is matched with no binding, placed in `context`."
  [kb [f sub super] context seen]
  (let [tax   (reasoning/taxonomy kb)
        idx   (:index kb)
        keyed (fn [k] (if (vector? k) (list sx/not-functor (list (second k))) (list k)))
        trig  (memoize (fn [k] (set (rules/trigger-keys tax (keyed k) idx))))
        rule-keys (delay (reads/as-stored-rule-keys idx))
        up    (if (sx/variable? super) (set (filter symbol? @rule-keys)) (trig super))
        down  (if (sx/variable? sub) (set (filter vector? @rule-keys)) (trig [:not sub]))
        gens  (generators-on kb (into up down))
        reads? (fn [ks] (some (fn [[_ g]] (some #(ks (rules/antecedent-key %)) (:antecedent g))) gens))
        closure (memoize (fn [dir p] (tax/signed-closure tax dir p nil)))
        floor (fn [r] [nil (tax/context-floor tax (map second r))])
        ;; {swapped? [routes-after routes-before]} for each parity `lo` reaches `hi` with
        ;; over the edge
        link  (memoize
               (fn [lo hi]
                 (let [old (parities (closure :up lo) hi)
                       new (reduce (fn [m [sw? rs]] (update m sw? (fnil into []) rs)) {}
                                   (for [p1 (parities (closure :down sub) lo)
                                         p2 (parities (closure :up super) hi)
                                         :let [sw? (not= (not= p1 (= 'genlInverse f)) p2)]]
                                     [sw? (for [r1 (link-routes tax lo sub p1) r2 (link-routes tax super hi p2)]
                                            (concat r1 [[nil context]] r2))]))]
                   (into {} (map (fn [[sw? rs]]
                                   (let [pre (when (contains? old sw?) (link-routes tax lo hi sw?))]
                                     [sw? [(tax/uncovered tax floor (concat pre rs)) pre]])))
                         new))))
        place (memoize (fn [fc [after before]]
                         (remove (set (firing-contexts tax fc before)) (firing-contexts tax fc after))))
        met   (fn [preds negative? ks]
                (for [s (->> (mapcat #(reads/as-stored-with-functor idx %) preds)
                             (keep #(v/sentex kb %))
                             (filter #(= negative? (vector? (rules/antecedent-key (:sentence %)))))
                             (nm/sort-by-content-key (juxt :sentence :context)))
                      :let [fp    (key-predicate (rules/antecedent-key (:sentence s)))
                            modes (fn [ak] (when (contains? ks ak)
                                             (let [q (key-predicate ak)]
                                               (if negative? (link q fp) (link fp q)))))]
                      t (placed-rules gens modes (:sentence s) (:context s) seen place)]
                  t))
        reach (fn [[st sw]] (into st sw))]
    (cond
      (empty? gens) []
      (or (sx/variable? sub) (sx/variable? super))
      (placed-rules gens #(when (contains? (into up down) %) {false [[]]}) nil context seen
                    (partial firing-contexts tax))
      :else
      (concat (when (reads? up) (met (reach (closure :down sub)) false up))
              (when (reads? down) (met (reach (closure :up super)) true down))))))

;; literal-reach and rule-placements call each other: a rule's conclusion is a literal,
;; and a literal that triggers a generator makes the engine write a rule.  `seen` holds
;; the generators already expanded on the path, so the descent ends.
(declare rule-placements)

(defn- literal-reach
  "The `[context why what]` triples storing literal `lit` in `context` writes: the context
  `assert` stores it in (`entry/storage-context`), CxUniverse beside it for a literal the
  store also lifts there (`special/lifts-to-universe?`), for a `genlCx` edge its lower
  context, whose ancestor set the edge widens, and the `rule-placements` of every rule
  storing it makes the engine write, in the context it is placed in (`generated-rules`,
  `edge-generated-rules`).  `::admin-only` for a
  literal no grant's contexts bound, `what` naming it: a placement declaration, a variable
  functor and a variable in place of a literal."
  [kb lit context seen]
  (let [f (when (sequential? lit) (first lit))]
    (cond
      (or (sx/variable? lit) (sx/variable? f))
      [[::admin-only "it may conclude any predicate" "a literal with a variable functor"]]
      (placement-declarations f)
      [[::admin-only "it places every (P …) the KB holds, in any context, in CxUniverse"
        (str "a " f " declaration")]]
      (nil? f)
      []
      :else
      (let [c (entry/storage-context kb f context)]
        (cond-> [[c nil]]
          (special/lifts-to-universe? kb f)
          (conj [sx/root-context (str "the store also deduces a (" f " …) into CxUniverse")])
          (and (= 'genlCx f) (= 3 (count lit)))
          (conj [(second lit) "a genlCx edge widens its lower context's ancestor set"])
          :always
          (into (mapcat (fn [[g r c']]
                          (rule-placements kb (sx/rule-consequent (rules/inner-rule r)) c'
                                           (cond-> seen g (conj g)))))
                (concat (generated-rules kb lit c seen)
                        (when (and (edge-functors f) (= 3 (count lit)))
                          (edge-generated-rules kb lit c seen)))))))))

(defn- conclusions
  "The `[literal context]` pairs a rule stored in `context` concludes from `consequent`:
  a conjunction, an existential head and a generated rule's consequent are descended, and
  a negation is the literal it is, as `entry/storage-context` and the lift read it."
  [consequent context]
  (cond
    (sx/variable? consequent)      [[consequent context]]
    (not (sequential? consequent)) []
    (= sx/and-functor (first consequent)) (mapcat #(conclusions % context) (rest consequent))
    (sx/head-exists? consequent)   (conclusions (sx/head-exists-body consequent) context)
    (sx/implies? consequent)       (conclusions (sx/rule-consequent consequent) context)
    :else                          [[consequent context]]))

(defn- rule-placements
  "The `[context why what]` triples a rule stored in `context` writes: `context`, and the
  `literal-reach` of every literal its `consequent` concludes."
  ([kb consequent context] (rule-placements kb consequent context #{}))
  ([kb consequent context seen]
   (into [[context nil]]
         (mapcat (fn [[lit c]] (literal-reach kb lit c seen)))
         (conclusions consequent context))))

(defn- placements
  "The `[context why what]` triples asserting `sentence` into `context` writes, as `assert`
  reads it: a `(set/monotonic …)` wrapper is looked through, an `(ist Ctx S)` names its
  own context, which wins, a rule is held to `rule-placements` and a fact to
  `literal-reach`.  `::admin-only` for a `do/` form, which stores nothing of its own and
  writes wherever its action does."
  [kb sentence context]
  (loop [s sentence, c context]
    (let [s (try (first (sx/peel-strength s nil))
                 (catch clojure.lang.ExceptionInfo _ s))]
      (cond
        (sx/do-form? s)
        [[::admin-only "it writes where its action does" "a do/ imperative"]]
        (entry/ist-parts s) (let [[c' s'] (entry/ist-parts s)] (recur s' c'))
        :else
        (let [s (try (rules/inner-rule s) (catch Exception _ s))]
          (if (sx/implies? s)
            (rule-placements kb (sx/rule-consequent s) c)
            (literal-reach kb s c #{})))))))

(defn- check-context!
  "Throw unless `grant` may write the `[c why what]` triple `placements` answers: `c` is
  in its `:writes`, or the grant is an admin's.  `why` says why the write reaches `c`; for
  `::admin-only`, `what` names what only an admin grant writes."
  [op {:keys [principal writes admin?]} [c why what]]
  (cond
    admin? nil
    (= ::admin-only c)
    (forbidden-context! op principal nil what (str why ", and only an admin grant writes it"))
    (not (contains? writes c))
    (forbidden-context! op principal c (pr-str c)
                        (str (some-> why (str ", and ")) "the token's grant does not name it"))))

(defn- stored-placements
  "The `[context why what]` triples the stored sentex `s` writes, read as `literal-reach`
  reads a literal: its context, CxUniverse beside it for a sentence the store also lifts
  there, `Sub` for a `(genlCx Sub Super)` edge, and `::admin-only` for a placement
  declaration."
  [kb s]
  (let [sentence (sx/sentence-of s)
        f        (when (sequential? sentence) (first sentence))
        why      (str "a rule the write fires concludes " (pr-str sentence))]
    (cond-> [[(:context s) (str why " there")]]
      (special/lifts-to-universe? kb f)
      (conj [sx/root-context (str why ", which the store also deduces into CxUniverse")])
      (and (= 'genlCx f) (= 3 (count sentence)))
      (conj [(second sentence) (str why ", which widens its lower context's ancestor set")])
      (placement-declarations f)
      (conj [::admin-only "it places every (P …) the KB holds, in any context, in CxUniverse"
             (str "a " f " declaration")]))))

(defn- write-check
  "The `entry/*write-check*` a write op runs under for `grant`, nil for no grant and for an
  admin's: a fn of the KB and the handles the write's rule firings concluded that throws
  `:forbidden-context` for the first, in content order, whose `stored-placements` names a
  context outside `:writes`.  `placements` does not predict those conclusions, and the
  throw takes the write back (docs/operations.md, \"The token table\")."
  [op {:keys [writes admin?] :as grant}]
  (when (and grant (not admin?))
    (fn [kb handles]
      (when-let [[_ t] (->> (for [h handles
                                  :let [s (v/sentex kb h)]
                                  :when s
                                  t (stored-placements kb s)
                                  :when (not (contains? writes (first t)))]
                              [s t])
                            (nm/min-by-content-key (fn [[s [c]]] [(sx/sentence-of s) (:context s) (nm/name-key c)])))]
        (check-context! op grant t)))))

(defn- check-placement!
  "Throw unless `grant` may store `sentence` asserted into `context`."
  [kb op grant sentence context]
  (run! #(check-context! op grant %) (placements kb sentence context)))

(defn- check-removal!
  "Throw unless `grant` may remove or annotate the sentex at `handle`.  A handle naming no
  stored sentex is nothing to remove, and for `:add-provenance` (`absent-ok?` false) it is
  refused: provenance written ahead of a sentex would be read as that sentex's own."
  [kb op {:keys [principal writes admin?]} handle absent-ok?]
  (let [sx (v/sentex kb handle)]
    (cond
      admin? nil
      (nil? sx) (when-not absent-ok?
                  (forbidden-context! op principal nil
                                      (str "provenance on handle " (pr-str handle))
                                      "the handle names no stored sentex"))
      (not (contains? writes (:context sx)))
      (forbidden-context! op principal (:context sx) (pr-str (:context sx))
                          (str "handle " (pr-str handle) " is stored there, and the token's"
                               " grant does not name it")))))

(defn- bounded-batch
  "An `edit` batch held to `grant`: every `:add` entry's placement checked and its opts
  given the principal (`with-identity`), every `:remove` handle's stored context
  checked.  A batch or an entry of the wrong shape is passed on as it came, for the op
  to refuse whole before it applies any of it."
  [kb op grant batch]
  (if-not (map? batch)
    batch
    (do (when (and grant (sequential? (:remove batch)))
          (doseq [h (:remove batch) :when (some? h)]
            (check-removal! kb op grant h true)))
        (cond-> batch
          (sequential? (:add batch))
          (update :add (fn [adds]
                         (mapv (fn [entry]
                                 (if (and (sequential? entry) (<= 2 (count entry) 3))
                                   (let [[s c o] entry
                                         o' (with-identity op grant o)]
                                     (if grant
                                       (do (check-placement! kb op grant s c) [s c o'])
                                       entry))
                                   entry))
                               adds)))))))

(defn- bound-write
  "`args` for write op `op`, held to `grant` — a token-table grant, or nil when the request
  presented none.  Under a grant every context a sentence's storage writes (`placements`),
  and every removed or annotated handle's stored context, must be one the grant writes
  (`:forbidden-context`), `:export` runs only under an admin grant, and the
  write records the provenance `:principal` and, unless an admin grant names another,
  the `:creator` as the grant's principal (`with-identity`; `:creator-mismatch` for a
  request naming an identity the grant does not hold).  Under no grant only a named
  `:principal` is refused.  Called inside the monitor, so a handle's stored context is
  read in the state the op runs on.  An `args` vector no arity of the op takes is passed
  on as it came, for the op's own `:bad-args`."
  [kb grant op args]
  (let [n   (count args)
        ctx (fn [i] (if (> n i) (nth args i) 'CxUniverse))
        put (fn [s c] (when grant (check-placement! kb op grant s c)))]
    (case op
      (:assert :try-assert)
      (if (<= 1 n 3)
        (do (put (nth args 0) (ctx 1))
            (if (or grant (= n 3))
              [(nth args 0) (ctx 1) (with-identity op grant (get args 2))]
              args))
        args)

      :assert-rule
      (if (<= 2 n 4)
        (do (when grant
              (run! #(check-context! op grant %) (rule-placements kb (nth args 1) (ctx 2))))
            (if (or grant (= n 4))
              [(nth args 0) (nth args 1) (ctx 2) (with-identity op grant (get args 3))]
              args))
        args)

      :assert-many
      (if (<= 2 n 3)
        (do (when (coll? (nth args 0))
              (doseq [s (nth args 0)] (put s (nth args 1))))
            (if (or grant (= n 3))
              [(nth args 0) (nth args 1) (with-identity op grant (get args 2))]
              args))
        args)

      :retract
      (do (when (and grant (= 1 n) (some? (nth args 0)))
            (check-removal! kb op grant (nth args 0) true))
          args)

      :add-provenance
      (if (= 2 n)
        (do (when (and grant (some? (nth args 0)))
              (check-removal! kb op grant (nth args 0) false))
            (check-claims! op grant (nth args 1))
            args)
        args)

      (:edit :edit-with-consequences)
      (if (<= 1 n 2)
        (assoc args 0 (bounded-batch kb op grant (nth args 0)))
        args)

      :export
      (do (when grant
            (check-context! op grant [::admin-only (str "op :export writes it to a directory"
                                                        " on the server's host")
                                      "the whole KB"]))
          args))))

(defn- off-worker
  "Run `thunk` on a `future` thread and wait for its value on this one, rethrowing what
  it threw.  An HTTP worker thread is the server's: Jetty interrupts it when the server
  stops, and an interrupt landing in a disk write closes the store's channel
  (`ClosedByInterruptException`) and latches the store unusable.  Nothing interrupts a
  `future` thread, so an interrupt reaches the worker's wait here and the op runs to the
  end of its write."
  [thunk]
  (let [fut (future (thunk))]
    (try @fut
         (catch ExecutionException e (throw (or (.getCause e) e))))))

(defn handle-op
  "Run one `{:op :args}` request under the write lock and answer with EDN.  The op runs
  on a thread of its own (`off-worker`), so stopping the server interrupts no KB write.

  Public because the browser serves the same protocol: `vaelii.browser.web` answers
  `POST /op` by calling this with its active KB, its own subscription registry and its
  own write monitor, so a native client reads the browser's KB with the daemon's op
  table, guards and refusals (docs/operations.md, \"The browser serves the protocol too\").

  The two guards run before the body is read.  `POST /op` is the write route of the
  single writer, and on an open loopback daemon nothing above has identified the
  caller, so a page the operator merely *visits* must not be able to drive it:
  `guard/edn-body?` forces a CORS preflight this daemon cannot answer, and
  `guard/same-origin?` refuses a browser that sent someone else's origin.  See
  `vaelii.host.guard`.

  Two tables are looked up, in order: the `vaelii.core` allowlist (`ops`, run under the
  monitor), then the daemon's own change-feed ops (`feed-ops`, which take the handler's
  subscription registry and decide about the monitor themselves — a long poll parks, and
  a parked poll holding it would block every writer).

  A write op (`write-ops`) is held to the grant the request's token carries
  (`guard/wrap-token-table` puts it on the request), inside the monitor, by
  `bound-write`.  A request with no grant, the browser's included, writes as before,
  except that it may not name the provenance `:principal`.

  `admit` is nil, or a fn of no arguments the op runs behind: called **inside** the
  monitor, before an engine op and before `:watch` registers, it answers nil to let the
  op run or `{:status :type :error}` to refuse it with that reply.  The browser passes one
  because its KB can be released while a request waits for the monitor, and only a check
  made inside the monitor sees that release.

  `host` is nil, or `{:ops :refuse}` from a process that serves this protocol beside
  something else: `:ops` maps op keywords to fns of the op's args the host answers itself,
  looked up before both tables and run outside the monitor, since they read the process
  rather than the KB; `:refuse` is a fn of no arguments asked before any other known op, nil
  to let it run or `{:status :ok false :type :error}` to refuse it.  The browser answers its catalog and
  job registry through the first, and refuses a KB op while a job writes the active KB
  through the second — which leaves the catalog readable while the KB it lists loads."
  ([kb registry monitor req] (handle-op kb registry monitor req nil))
  ([kb registry monitor req admit] (handle-op kb registry monitor req admit nil))
  ([kb registry monitor req admit host]
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
         ;; client discriminates on `:type` rather than on the status code.  A body that
         ;; ends before its `Content-Length` is the same fault, one step earlier.
         (let [body (try (guard/read-capped-body req)
                         (catch java.io.IOException t
                           (throw (ex-info (str "request body did not arrive whole: "
                                                (.getMessage t))
                                           {:type :not-edn}))))
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
               grant (::guard/grant req)
               h (get (:ops host) op)
               f (when-not h (ops op))
               g (when-not (or h f) (feed-ops op))
               no (when-let [refuse (when (or f g) (:refuse host))] (refuse))]
           (cond
             h
             (edn-reply 200 {:ok true :result (off-worker #(wire-safe (h (vec args))))})

             no
             (edn-reply (:status no) {:ok false :type (:type no) :error (:error no)})

             ;; `wire-safe` inside the monitor, not after it: the walk is what *realizes*
             ;; a lazy answer stream, so releasing the lock around the call alone would
             ;; let a `:query` read its matches while a concurrent `:assert` is settling
             ;; — one reply straddling two states of the KB.  The daemon promises reads
             ;; pay the same lock, and the read is not over until its seq is.
             ;; an arity mismatch at the entry point is the caller naming the wrong number
             ;; of args, so it is a 400 like the unknown op beside it; one raised inside the
             ;; op is a server fault and keeps its 500
             f
             (let [result (try (off-worker
                                #(locking monitor
                                   (admit! admit)
                                   (wire-safe
                                    (binding [entry/*write-check* (when (write-ops op)
                                                                    (write-check op grant))]
                                      (f kb (cond->> (vec args)
                                              (write-ops op) (bound-write kb grant op)))))))
                               (catch clojure.lang.ArityException t
                                 (if (entry-arity-error? f t)
                                   (throw (ex-info (str "wrong number of arguments for op "
                                                        (pr-str op) ": " (.getMessage t))
                                                   {:type :bad-args :op op}))
                                   (throw t))))]
               (edn-reply 200 {:ok true :result result}))

             ;; the feed's own, **outside** the monitor here — each takes it for itself
             ;; where it needs it, and `:poll` must not, since a parked long poll holding
             ;; the daemon's one lock would stall every writer for the length of its wait.
             ;; Nothing a feed op answers is a lazy stream over the store, so realizing it
             ;; out here straddles no state: the events were built at settle time and are
             ;; already values.
             g
             (edn-reply 200 {:ok true
                             :result (off-worker
                                      #(wire-safe (g {:kb kb :registry registry :monitor monitor
                                                      :admit admit}
                                                     (vec args))))})

             :else
             (edn-reply 400 {:ok false :error (str "unknown op: " (pr-str op))
                             :type :unknown-op
                             :ops (vec (sort (into op-names (keys (:ops host)))))}))))
       (catch clojure.lang.ExceptionInfo e
         (let [ty (:type (ex-data e))]
           (cond
             (::status (ex-data e))
             (edn-reply (::status (ex-data e)) {:ok false :error (.getMessage e) :type ty})
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
                         :type (:type (ex-data t) :internal-error)}))))))

;; ---- authentication: one shared bearer token, or the token table ---------

(def ^:private open-routes
  "The routes that answer before the token is checked, and `GET /health` is the whole
  set.  A daemon only its token-holder can probe is one no container orchestrator, load
  balancer or shell script can watch, and `{:ok true}` tells a caller nothing it did not
  already know by connecting.  Stated here because an unauthenticated route inside an
  authenticated daemon looks like an oversight to delete: this one is a decision."
  #{"/health"})

(defn- unauthorized
  "The daemon's 401: EDN carrying a non-nil `:type` like every other refusal the daemon can
  answer, plus the `WWW-Authenticate` challenge a 401 is defined to carry."
  [_]
  {:status 401
   :headers {"content-type" "application/edn"
             "www-authenticate" "Bearer"}
   :body (pr-str {:ok false :type :unauthorized
                  :error "this daemon requires Authorization: Bearer <token>"})})

(defn- wrap-bearer-auth
  "`handler` behind the token table when `table` is set (`guard/wrap-token-table`, each
  request carrying its token's grant to `handle-op`), else behind the shared `token`
  (`guard/wrap-bearer`).  A table set leaves the shared token unread.  The comparison and
  the header read are the browser's too, and live in `vaelii.host.guard` for that reason."
  [handler token table]
  (if table
    (guard/wrap-token-table handler table open-routes unauthorized)
    (guard/wrap-bearer handler token open-routes unauthorized)))

(def http-threads
  "How many worker threads the daemon's HTTP server runs.

  Stated rather than defaulted, because it is one half of a pair: a parked long poll
  holds one of these for the length of its wait, so `subscribe/max-parked` has to stay
  well under it or the feature that exists for liveness becomes the thing that stalls
  the daemon.  Left implicit the two numbers were 50 and 64, the wrong way round, and
  nothing said so — 55 parked polls took `/health` from 62 ms to 26 s.  `serve_test`
  asserts the relationship."
  50)

(def ^:private loopback
  "The network interface the daemon binds unless told otherwise.  `POST /op` is the **write**
  route of the single writer, so it answers only the machine it runs on; exposing it is
  an explicit choice (`--listen`), not the default.  The same rule the browser holds to
  (`vaelii.browser.web`), and the more important of the two — the browser edits a KB, and
  this one *is* the KB's only writer.

  Loopback bounds *which machine* may reach the daemon and nothing more: a browser on
  that machine is a local client too, which is what `vaelii.host.guard` is for, and
  every other process on it is a client with a socket, which is what the bearer token
  is for.  A loopback daemon may run open; one that binds an address may not
  (`auth-posture`)."
  "127.0.0.1")

(defn- daemon-state
  "What one handler owns: the write monitor its ops serialize on, the subscription
  registry its feed tokens name, and `:open?`, which `stop-ops` clears."
  []
  {:monitor (Object.)
   ;; per handler, beside the monitor and for the same reason: a feed token names a
   ;; subscription *on this daemon*, so it is state the handler owns rather than state
   ;; the KB does — two handlers over one KB are two daemons, and a token from one
   ;; means nothing to the other
   :registry (sub/registry)
   :open? (atom true)})

(defn- stop-ops
  "Refuse every op of `state`'s handler that has not entered the monitor (503
  `:stopping`), answer every parked long poll with the events it has
  (`sub/release-parked`), then wait for the op inside the monitor to finish.  `start`
  calls this as its server begins to stop, before Jetty interrupts a worker or closes a
  connector, so the op in progress answers its caller."
  [{:keys [monitor registry open?]}]
  (reset! open? false)
  (sub/release-parked registry)
  (locking monitor nil))

(defn- opts-table
  "The token table `opts` names under `:token-table` — a map (`guard/check-token-table`) or
  the path of an EDN file (`guard/read-token-table`) — or, when `opts` names neither
  `:token-table` nor `:token`, `VAELII_TOKEN_TABLE`'s.  A caller naming `:token` alone has
  chosen the shared token, so the variable is not read.  An explicit nil is no table."
  [opts]
  (cond
    (contains? opts :token-table)
    (let [t (:token-table opts)]
      (cond (nil? t) nil
            (map? t) (guard/check-token-table t ":token-table")
            :else    (guard/read-token-table t)))
    (contains? opts :token) nil
    :else (guard/token-table)))

(defn- handler
  [kb {:keys [host] :or {host loopback} :as opts} {:keys [monitor registry open?]}]
  (let [token   (if (contains? opts :token) (:token opts) (guard/api-token))
        table   (opts-table opts)
        allowed (guard/allowed-hosts host)
        admit   (fn [] (when-not @open?
                         {:ok false :status 503 :type :stopping
                          :error "the daemon is stopping; this op did not run"}))]
    (wrap-bearer-auth
     (guard/wrap-host-allowed
      (ring/ring-handler
       (ring/router
        [["/health" {:get (fn [_] {:status 200
                                   :headers {"content-type" "application/edn"}
                                   :body (pr-str {:ok true})})}]
         ["/op" {:post (fn [req] (handle-op kb registry monitor req admit))}]])
       (ring/create-default-handler
        {:not-found (fn [req]
                      {:status 404 :headers {"content-type" "application/edn"}
                       ;; typed like every other {:ok false} — the migration
                       ;; line "every reply carries a non-nil :type" holds on
                       ;; this route too, not only on POST /op
                       :body (pr-str {:ok false
                                      :error (str "no route for "
                                                  (str/upper-case (name (:request-method req :get)))
                                                  " " (:uri req) " — the daemon answers POST /op"
                                                  " and GET /health")
                                      :type :not-found})})}))
      allowed
      (fn [_] {:status 400
               :headers {"content-type" "application/edn"}
               :body (pr-str {:ok false :type :bad-host
                              :error "unrecognized Host header"})}))
     token table)))

(defn app
  "The ring handler for a KB — pure `request -> response`, so it is tested without a
  socket.  One monitor per handler serializes the ops (the single-writer contract).

  `:host` names the interface this handler will be served on, which fixes the `Host`
  values it answers to (`guard/allowed-hosts`).  On the loopback default that refuses
  a rebound DNS name, the one attack `same-origin?` cannot see.

  `:token` is the shared bearer token every request must present.  Omitted, it is
  `VAELII_API_TOKEN` (`guard/api-token`), so a daemon and a client on one host agree
  without either being configured; an explicit nil serves **open**, which is what a
  test of the other refusals needs — a handler that 401s first exercises none of them.

  `:token-table` is the per-principal token table, a map or the path of an EDN file
  (`guard/check-token-table`).  Omitted with `:token` omitted too, it is
  `VAELII_TOKEN_TABLE`'s (`guard/token-table`); omitted beside a `:token`, or an explicit
  nil, it is none.  Set, it replaces `:token`: a request
  presents a token the table holds, and a write op lands only in the contexts that token's
  grant names (`bound-write`).  A table that does not check is refused
  (`:bad-token-table`)."
  ([kb] (app kb {}))
  ([kb opts] (handler kb opts (daemon-state))))

(defn start
  "Start the daemon over `kb` and return the running jetty `Server` (`:join? false`, so
  the caller controls its lifetime — a test stops it in a `finally`).  `:port 0` binds
  an ephemeral port; read the actual one with `port`.

  `:host` defaults to loopback; pass an address (`\"0.0.0.0\"`) to bind publicly, and
  read the note on `loopback` before doing so.  `:token` and `:token-table` are `app`'s,
  each forwarded only when the key is there, so an omitted one still reads its variable
  and an explicit nil `:token` serves open on loopback.  An address with neither a token
  nor a table is refused (`guard/require-token!`), and so is a table that does not check
  (`:bad-token-table`), both before anything binds, as `-main` refuses them.

  `.stop` on the server first runs `stop-ops`: an op that has not entered the monitor
  answers 503 `:stopping`, and the stop returns after the op inside it finishes."
  ^Server [kb {:keys [port host] :or {port 4200 host loopback} :as opts}]
  (let [table (opts-table opts)]
    (when-not table
      (guard/require-token! "daemon" host (if (contains? opts :token) (:token opts) (guard/api-token))))
    (let [state  (daemon-state)
          h      (handler kb (assoc (select-keys opts [:token]) :host host :token-table table)
                          state)
          server (jetty/run-jetty h
                                  {:port port :host host :join? false :max-threads http-threads})]
      (.addEventListener ^Server server
                         (reify LifeCycle$Listener
                           (lifeCycleStopping [_ _] (stop-ops state))))
      server)))

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
                                                             " [<dir>] [--listen <address>]"
                                                             " [--starter]")
                                                        {:type :unknown-option :mismatch :unknown-key :arg (nth pos 2)}))
                                        pos)
      (= "--listen" a)                (recur (rest more) pos)   ; value read by listen-host
      (= "--starter" a)               (recur more pos)          ; read by -main
      (.startsWith ^String a "--")    (throw (ex-info (str "unknown flag: " a " — the"
                                                           " daemon reads --listen"
                                                           " <address> and --starter,"
                                                           " and takes a port"
                                                           " and a store directory as"
                                                           " positionals")
                                                      {:type :unknown-option :mismatch :unknown-key :flag a}))
      :else                           (recur more (conj pos a)))))

(def ^:private public-bind?
  "`guard/public-bind?` — the same question the browser asks, so the bind that requires
  a token is the same bind on both servers."
  guard/public-bind?)

(defn- auth-posture
  "Which posture a daemon binding `host` with `token` and the token `table` runs in — and
  the refusal when neither credential is available.

    :per-principal  a token table is set: every request presents one of its tokens, and a
                    write lands only in that token's grant
    :required       a token is set, and every request presents it
    :open           loopback with neither: every process on this machine drives the writes

  **A bind that names an address with no token and no table is refused** (`guard/require-token!`,
  `:unauthorized`), which is the one place the daemon fails closed, and the browser is
  held to the same rule by the same fn.  It is the flag that publishes `POST /op` — the
  KB's only writer — and the same flag drops the `Host` allowlist, so the exposed
  configuration would otherwise be the one with the fewest checks.  The loopback
  default is not held to it because `lein serve` on a laptop is a real workflow that a
  required credential would only teach an operator to export a constant.  The `Host`
  allowlist is not held to it either — see `host-posture` for why that one warns
  instead of refusing."
  [host token table]
  (if table
    :per-principal
    (do (guard/require-token! "daemon" host token)
        (if (str/blank? token) :open :required))))

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
  (case posture
    :per-principal
    (do (trove/log! {:level :info :id ::per-principal
                     :msg (str "every request must carry a token VAELII_TOKEN_TABLE holds, and"
                               " a write lands only in the contexts its grant names")})
        (when (guard/api-token)
          (trove/log! {:level :warn :id ::token-unread
                       :msg (str "VAELII_API_TOKEN is set and unread: under VAELII_TOKEN_TABLE"
                                 " only the table's tokens authenticate")})))
    :required
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

(defn- dir-backend
  "The backend the daemon opens `dir` under: the one the store there was written by
  (`v/store-backend`), else `:disk-log` for a directory holding no store yet.  A
  `:disk-snapshot` or `:disk-columnar` store opened as `:disk-log` finds no index log, so
  every client read against it answers nothing although every record is on disk."
  [dir]
  (or (v/store-backend dir) :disk-log))

(defn -main
  "Run the daemon in the foreground.  Args: `[port [dir]] [--listen ADDR] [--starter]`,
  in any order — `dir` opens the store there under the backend its files were written by,
  or a new durable `:disk-log` store when it holds none (`dir-backend`); either is
  recovered on open, so it persists across restarts.  With no `dir` the KB is in-memory
  and lives only as long as the process.

  `--starter` loads the shipped starter schema (`vaelii.host.starter/load-into`) into the
  KB after it opens and before the port is bound, so `GET /health` answers only once the
  schema is in.  The load asserts every starter sentence: into a directory that already
  holds them, each dedups to its stored handle, and the load still reads every file.

    lein run -m vaelii.host.serve 4200 /var/lib/vaelii
    lein run -m vaelii.host.serve 4200 --starter                          ; in memory, with the schema
    lein run -m vaelii.host.serve 4200 /var/lib/vaelii --listen 0.0.0.0   ; opt-in

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
        [table posture] (try (let [table (guard/token-table)]
                               [table (auth-posture host token table)])
                             (catch clojure.lang.ExceptionInfo e
                               (binding [*out* *err*] (println (ex-message e)))
                               (System/exit 2)))
        hosts (host-posture host)
        starter? (boolean (some #{"--starter"} args))
        kb    (cond-> (if dir
                        (v/open-kb {:backend (dir-backend dir) :dir dir :reasoners :stored})
                        (v/open-kb {}))
                starter? starter/load-into)]
    (trove/log! {:level :info :id ::start
                 :msg "vaelii daemon listening"
                 :data {:port port :host host :dir (or dir :memory)
                        :starter starter? :auth posture :hosts hosts}})
    (announce-auth! host posture hosts)
    ;; shrink the derived caches when the heap the daemon runs in fills, and grow them back
    ;; as it frees — the daemon owns one KB, so the guard's KB list is that one
    (caches/install-memory-guard! {:kbs (fn [] [kb])})
    ;; `:max-threads` here as in `start`: `http-threads` is one half of the pair
    ;; `subscribe/max-parked` is checked against, and a daemon run from the command line
    ;; has to hold the same relationship as one a test starts
    (jetty/run-jetty (app kb {:host host :token token :token-table table})
                     {:port port :host host :join? true :max-threads http-threads})))
