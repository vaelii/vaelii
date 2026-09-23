;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.config
  "The build's switches — the `vaelii.*` JVM system properties and the `VAELII_*`
  environment variables — read in one place, each against a domain, and **refused when
  the value is outside it**.

  This is `kb/check-opts!`'s invariant one layer out: *an option that is not read is not
  an option*.  A switch read as a membership test or an equality against one spelling has
  no wrong value — every misspelling falls to the other branch — so under that reading
  `vaelii.disk.auto-compact=disabled` is compaction **on** and `vaelii.disk.fsync=always`
  is the three-second tick, which is the durability level the operator is trying to
  leave.  A process that reports itself configured and is not is the failure
  `check-opts!` exists to prevent, on the property that decides whether a crash loses
  data.  So no switch is read that way here.

  ## One vocabulary for the boolean switches

  `truthy` and `falsy` below, case-insensitively, and nothing else: every boolean switch
  reads the same words, so a spelling that works on one works on all of them and a
  spelling that works on none is an error rather than the opposite setting.  A blank
  value is *unset* — an exported-but-empty environment variable is the shell's way of
  saying nothing.

  ## Where a refusal lands

  `check!` reads every switch at `kb/open-kb`, so a wrong value fails the open — before a
  record is written and while what the operator typed is still legible.  It reads the
  whole set rather than the ones this KB's backend uses, because gating the check on the
  configuration is how a wrong value in the configuration escapes it.

  Where each switch is read **besides** that is the `:read-at` column of `switches`, and
  `read-at-kinds` says what the three values mean.  It is a column rather than a list of
  names here for the reason `check!` is a walk rather than a list of calls: a roster
  spelled twice is one that can disagree with itself, and this one had.

  The two that make the eager read worth its cost are visible there as `:worker` and
  `:load`.  A `:worker` row is read inside `fsync-all`'s `catch Throwable`, which logs an
  exception's class name and nothing else — an unattributable line repeating every three
  seconds with auto-compaction silently dead.  A `:load` row is the root value of a var
  and cannot be deferred at all; it refuses at that namespace's load, naming itself, for
  `guard/max-body-bytes`' reason: a silent fallback leaves an operator believing a setting
  they never made, and a raw parse failure out of a `def` reports as a namespace that
  would not load rather than as the typo it is.  `log-level` is `:load` for a different
  reason — it is the one switch whose effect is an *install*, and the entry point it belongs at
  is the moment the engine is loaded rather than the moment a KB is opened.

  ## What is not checkable here

  Five switches name a path or a label with no domain to check — `vaelii.disk.dir`,
  `vaelii.kb.path`, `vaelii.kb.catalog`, `vaelii.build`, `vaelii.clingo.lib` — and one
  names a member of a registry that resolves it itself: `vaelii.llm.provider`
  (`llm.provider/configured`).  `vaelii.web.port` / `VAELII_WEB_PORT` is the browser's
  own, read at `web/default-port`, where an unparseable value falls through to the next
  source rather than stopping a start over a convenience variable (docs/web.md).

  Three more belong to the two servers and are read at `vaelii.host.guard`, which both
  of them read: `VAELII_API_TOKEN` and `VAELII_ALLOWED_HOSTS` are a secret and a host
  list, neither of which has a domain to hold them to, and the ceiling
  `VAELII_MAX_BODY_BYTES` refuses at `guard/max-body-bytes` for the reason
  `arbitrate-constraints?` refuses at load — it is the root value of a var."
  (:require [clojure.string :as str]))

(def truthy
  "The spellings that mean **on**, for every boolean switch.  One vocabulary rather than
  one per switch: a word that works for one switch works for all of them, so nothing is
  learned about `vaelii.disk.tokens` that is false of `vaelii.disk.auto-compact`."
  #{"true" "1" "on" "yes"})

(def falsy
  "The spellings that mean **off**.  Wider than `\"false\"` because the disk switches
  document `0` / `off` / `no` as well, and removing an accepted spelling breaks a setup
  that works."
  #{"false" "0" "off" "no"})

(defn- raw
  "The value of `nm` — a system property when it is spelled like one, an environment
  variable when it is spelled in caps — trimmed, or nil when unset or blank.  The
  spelling picks the source so a call site reads as one line; nothing in the tree names
  a switch both ways."
  [^String nm]
  (let [v (if (re-find #"^[A-Z]" nm) (System/getenv nm) (System/getProperty nm))]
    (when-not (str/blank? v) (str/trim v))))

(defn- refuse!
  "The one refusal shape: the switch, the value it was given, and what it accepts —
  named in the message, because an operator reading a log has only the message.  `data`
  carries the domain in whatever shape the domain has."
  [nm value want data]
  (throw (ex-info (str nm "=" value " is not a value " nm " reads — want " want)
                  (merge {:type :unknown-option :mismatch :bad-value :switch nm :property nm :value value}
                         data))))

(defn- boolean-vocabulary [] (vec (concat (sort truthy) (sort falsy))))

(defn prop-bool
  "`nm` as a boolean, `default` when unset.  Anything outside `truthy` / `falsy` is
  refused rather than read as the falsy branch, which is where `=disabled` meaning
  *enabled* came from."
  [nm default]
  (if-let [v (raw nm)]
    (let [s (str/lower-case v)]
      (cond
        (truthy s) true
        (falsy s)  false
        :else      (refuse! nm v (str "one of " (str/join ", " (boolean-vocabulary)))
                            {:accepted (boolean-vocabulary)})))
    default))

(defn prop-enum
  "`nm` as the value `accepted` maps its (lower-cased) spelling to, `default` when unset.
  `want` is the prose the refusal offers instead — a roster alone answers *what is
  legal* and not *what the legal one does*, and the second is what the operator who
  typed the wrong one needs."
  [nm accepted default want]
  (if-let [v (raw nm)]
    (let [s (str/lower-case v)]
      (if (contains? accepted s)
        (get accepted s)
        (refuse! nm v want {:accepted (vec (sort (keys accepted)))})))
    default))

(defn- refuse-number!
  "A number outside its domain, refused with the domain spelled as a range rather than
  as a roster — `0 to 1` says what `[0 1]` does not."
  [nm v kind lo hi]
  (refuse! nm v (str kind (cond (and lo hi) (str " from " lo " to " hi)
                                lo          (str ", " lo " or more")
                                :else       ""))
           {:min lo :max hi}))

(defn- prop-number
  "`nm` parsed by `parse`, `default` when unset, refused outside `lo`/`hi`.  The body the
  two readers below share; `kind` is the noun the refusal spells, and it is the only
  thing besides the parser that ever differed between them.

  The bound test compares the parsed number rather than a coercion of it, so a whole
  number past a double's exact range is still bounded exactly — the values read here are
  capacities and byte caps, which is precisely where a caller can name one that large."
  [nm default lo hi kind parse]
  (if-let [v (raw nm)]
    (let [n (try (parse v)
                 (catch NumberFormatException _
                   (refuse-number! nm v kind lo hi)))]
      (when (or (and lo (< n lo)) (and hi (> n hi)))
        (refuse-number! nm v kind lo hi))
      n)
    default))

(defn prop-long
  "`nm` as a long, `default` when unset.  `lo`/`hi` bound it — every count read here is a
  duration or a capacity, so one below zero is a typo rather than a setting."
  [nm default lo hi]
  (prop-number nm default lo hi "a whole number" #(Long/parseLong ^String %)))

(defn prop-double
  "`nm` as a double, `default` when unset, bounded by `lo`/`hi` as `prop-long` is."
  [nm default lo hi]
  (prop-number nm default lo hi "a number" #(Double/parseDouble ^String %)))

;; ---- the switches -------------------------------------------------------
;; One accessor per switch, holding its domain and its default.  The call sites read
;; through these, so the domain a value is refused against is the same one the reader
;; honours — a second spelling of either is how the two drift apart.

(defn disk-auto-compact?
  "Is background and opportunistic compaction on (`vaelii.disk.auto-compact`, default
  on)?  Read by the fsync tick and by the close path — one knob, not two."
  []
  (prop-bool "vaelii.disk.auto-compact" true))

(defn disk-fsync-mode
  "`vaelii.disk.fsync`: `:dsync` opens every log `rwd`, so an append is durable when it
  returns; `:tick` (the default, and what unset means) leaves durability to the
  `vaelii.disk.sync-ms` daemon."
  []
  (prop-enum "vaelii.disk.fsync" {"dsync" :dsync} :tick
             (str "\"dsync\" (fsync every append) or unset (the vaelii.disk.sync-ms"
                  " tick)")))

(defn disk-compress
  "`vaelii.disk.compress`: `:zstd`, `:lz4`, or nil for uncompressed frames (the
  default).  A `case` with a nil default arm is what made `=gzip` and `=zstdd` read as
  no compression at all — a store written smaller than the operator asked for, with
  nothing to say so."
  []
  (prop-enum "vaelii.disk.compress"
             {"none" nil "off" nil "false" nil "zstd" :zstd "lz4" :lz4}
             nil
             "zstd, lz4, or none"))

(defn disk-tokens?
  "Are sentex bodies written as token ids (`vaelii.disk.tokens`, default off)?  Off
  because it is the one part of the record store that adds a durable ground truth, so a
  store opts in.  *Reading* is never gated on it — a frame carries its own tag."
  []
  (prop-bool "vaelii.disk.tokens" false))

(defn disk-cache-capacity
  "Hot records held per kind (`vaelii.disk.cache`, default 65536; 0 disables the cache).
  A count, so it is read at the record store's open rather than at namespace load: a
  `Long/parseLong` in a top-level `def` turns `=64k` into a namespace that will not
  load, which reports the typo as a broken build."
  []
  (prop-long "vaelii.disk.cache" 65536 0 nil))

(defn disk-sync-ms
  "The durability daemon's tick, in milliseconds (`vaelii.disk.sync-ms`, default 3000;
  0 disables the daemon)."
  []
  (prop-long "vaelii.disk.sync-ms" 3000 0 nil))

(defn disk-compact-dead-ratio
  "The dead ratio a log must reach to be worth compacting
  (`vaelii.disk.compact-dead-ratio`, default 0.5).  A ratio, so outside 0–1 it is a
  threshold that either never fires or fires on every tick."
  []
  (prop-double "vaelii.disk.compact-dead-ratio" 0.5 0 1))

(defn disk-compact-min-interval-ms
  "The floor between two auto-compactions of one backend
  (`vaelii.disk.compact-min-interval-ms`, default 300000)."
  []
  (prop-long "vaelii.disk.compact-min-interval-ms" 300000 0 nil))

(defn disk-lock?
  "Is the single-writer `FileLock` taken when a directory opens (`vaelii.disk.lock`,
  default on)?  Off is for a filesystem whose `FileLock` is unreliable, and it removes
  the enforcement rather than the contract."
  []
  (prop-bool "vaelii.disk.lock" true))

(defn index-snapshot?
  "Refuse `vaelii.index.snapshot`, naming the backend that selects the image instead.

  The image is an index **representation**, and a representation is named in the opts map
  where a reader of the KB's own configuration can see it: `{:backend :disk-snapshot}`,
  the one pairing there is.  A process-wide property cannot say that — the same opts map
  means a mapped index on one machine and an hour of `reindex` on another, with nothing
  on the KB to tell them apart, which is the failure this namespace's `check!` exists to
  close.

  Refused rather than read as a default, on the argument `kb/reserved-backend-names`
  makes for `:disk`: a switch that silently does nothing is discovered by the operator
  running out of the resource they thought they had bought.

  Read through `raw` rather than a `prop-*` helper because the domain is **empty**: there
  is no value to parse and no default to fall back to.  The name is still one the build
  reads, so it is on the pinned configuration surface with every other switch
  (`config_surface_test`) and carries its own row in docs/operations.md — an operator
  whose unit file sets it meets a refusal at the open, and a refusal naming a switch no
  document admits to leaves them reading the source for it."
  []
  (when-let [v (raw "vaelii.index.snapshot")]
    (throw (ex-info (str "vaelii.index.snapshot=" v " is not a switch this build reads"
                         " — the mapped index image is an index representation, selected"
                         " as {:backend :disk-snapshot}, so the KB's own opts record that"
                         " it was asked for.  Unset the property and name the backend.")
                    {:type :unknown-option :mismatch :unknown-key :switch "vaelii.index.snapshot"
                     :property "vaelii.index.snapshot" :value v
                     :remedy {:backend :disk-snapshot}})))
  nil)

(defn index-snapshot-drift
  "How far the live index may drift from its image before the writer refreshes it
  (`vaelii.index.snapshot-drift`, default 0.5) — a ratio, as
  `vaelii.disk.compact-dead-ratio` is, and read the same way.

  Drift is measured in **indexed roots**: the count now, against the count the image
  holds, over the count the image holds.  Roots rather than trie nodes because a node
  count is a measurement the store has to take and a root count is one it already has —
  the same lesson `disk/durability.clj` learned when it found the record store scanning
  every `.idx` to answer a dead ratio on a three-second tick."
  []
  (prop-double "vaelii.index.snapshot-drift" 0.5 0 1))

(defn belief-snapshot?
  "Refuse `vaelii.belief.snapshot`, naming the backend that writes and installs a belief
  image instead.

  A reasoning image is written and installed for a `{:backend :disk-snapshot}` KB on the
  dense network (`vaelii.impl.reasoning-image`), the same KB whose index is read from an
  image, and no property turns it on or off.  Refused rather than ignored, on
  `index-snapshot?`'s argument: an operator whose unit file sets it meets a refusal at the
  open instead of a switch that does nothing."
  []
  (when-let [v (raw "vaelii.belief.snapshot")]
    (throw (ex-info (str "vaelii.belief.snapshot=" v " is not a switch this build reads"
                         " — a reasoning image is written and installed for a"
                         " {:backend :disk-snapshot} KB, so the KB's own opts record that"
                         " it was asked for.  Unset the property and name the backend.")
                    {:type :unknown-option :mismatch :unknown-key :switch "vaelii.belief.snapshot"
                     :property "vaelii.belief.snapshot" :value v
                     :remedy {:backend :disk-snapshot}})))
  nil)

(defn arbitrate-constraints?
  "Does the process default to arbitrating a definitional clash rather than refusing it
  (`VAELII_ARBITRATE_CONSTRAINTS`, default off)?  A KB naming a `:constraints` policy
  overrides it."
  []
  (prop-bool "VAELII_ARBITRATE_CONSTRAINTS" false))

(defn assertive-arg-types?
  "Do the argument constraints entail as well as constrain (`VAELII_ASSERTIVE_ARG_TYPES`,
  default on)?  `VAELII_ASSERTIVE_ARG_TYPES=0` opts out, back to the constraint-only
  reading."
  []
  (prop-bool "VAELII_ASSERTIVE_ARG_TYPES" true))

(defn prune-subsumed-mints?
  "Does a minted argument type give way to a more specific membership the KB believes
  (`VAELII_PRUNE_SUBSUMED_MINTS`, default **off**)?  `=1` opts in: the KB stores about a
  tenth fewer sentexes and answers exactly what it answered before (docs/argtypes.md).
  Off by default for what it costs rather than for what it does — a settle that moves a
  membership asks what that membership displaces, which is measured at +42% on a
  settle-dense workload.  Read only where the entailment runs at all, so it does nothing
  with `VAELII_ASSERTIVE_ARG_TYPES=0`."
  []
  (prop-bool "VAELII_PRUNE_SUBSUMED_MINTS" false))

(defn cache-scale
  "The multiplier applied to every in-memory derived cache's shipped entry limit
  (`VAELII_CACHE_SCALE`, default 1.0).  Below 1 shrinks the caches for a small-heap
  embedding; above 1 grows them for a bulk load.  A per-cache floor keeps a small scale
  from taking a cache below the point where it saves nothing
  (`vaelii.impl.caches/min-limit`).  Read at `vaelii.impl.caches`' load, so a value that is
  not a number, or is below zero, refuses there naming the switch."
  []
  (prop-double "VAELII_CACHE_SCALE" 1.0 0 nil))

(defn web-dev?
  "Is the browser a development server (`VAELII_DEV`, default off)?  A value, not mere
  presence: `VAELII_DEV=0` says off and read as presence it said on."
  []
  (prop-bool "VAELII_DEV" false))

(defn profiler?
  "Should the sampling profiler's UI be started with the browser (`VAELII_PROFILER`,
  default off)?

  Off by default and asked for explicitly, because starting it is not free and not
  private: the profiler attaches an agent to this JVM and serves flamegraphs on a second
  port with no authentication of its own.  A reader who wants one says so."
  []
  (prop-bool "VAELII_PROFILER" false))

(defn profiler-port
  "The port the profiler's UI binds (`VAELII_PROFILER_PORT`, default 8080).  Read only
  when `profiler?` says to start one."
  []
  (prop-long "VAELII_PROFILER_PORT" 8080 1 65535))

(def asp-solver-spellings
  "What the ASP backend switch reads, one spelling per backend.  Unset is **auto** —
  in-process clingo when it loads, else clasp — which is why the reader's default is nil
  rather than a backend: `auto` is the absence of a choice, not a third one to name."
  {"clingo" :clingo "clasp" :clasp})

(defn asp-solver
  "Which ASP backend solves (`vaelii.asp.solver`, else `VAELII_ASP_SOLVER`), or **nil**
  for auto.  The property is read first, and both spellings refuse a name outside the
  roster: read as a bare `(keyword …)` a misspelt backend became a keyword nothing
  matches and the selector's fallback arm ran **auto**, so a run pinned to clasp could
  silently use clingo and report a clean pass for a backend nothing exercised."
  []
  (or (prop-enum "vaelii.asp.solver" asp-solver-spellings nil "clingo or clasp")
      (prop-enum "VAELII_ASP_SOLVER" asp-solver-spellings nil "clingo or clasp")))

(defn clingo-max-program-bytes
  "The plain-ASP program size above which **auto** routes to clasp even where clingo
  loads (`VAELII_CLINGO_MAX_BYTES`, default 3000).  An explicit backend ignores it."
  []
  (prop-long "VAELII_CLINGO_MAX_BYTES" 3000 0 nil))

(defn asp-time-limit
  "The seconds **one ASP solve** may run before the backend is interrupted
  (`VAELII_ASP_TIME_LIMIT`, default 60; 0 lifts the limit).  Both backends honour it —
  clasp through `--time-limit`, in-process clingo by cancelling the solve handle — and
  an interrupted solve reports `:interrupted`, which no consumer treats as an answer
  (`asp.edge`): the edge solver decides nothing and an imperative refuses.

  A solve runs on the single writer, so an unbounded one holds every write behind it —
  but an **operation** makes as many solves as it needs, each with the whole budget: two
  for a classification, three for `do/labeling`, one per defeat round for a settle.
  docs/asp.md tabulates the multipliers, and a test pins the counts so the table cannot
  drift from them."
  []
  (prop-long "VAELII_ASP_TIME_LIMIT" 60 0 nil))

(def log-level-spellings
  "What `VAELII_LOG_LEVEL` reads, one spelling per level the dial takes.  A def rather
  than a literal inside the reader so that the environment and
  `vaelii.core/set-log-level` can be checked to admit the same five: two rosters for one
  dial is one of them wrong."
  {"error" :error "warn" :warn "info" :info "debug" :debug "trace" :trace})

(defn log-level
  "The level the engine's own logging prints at (`VAELII_LOG_LEVEL`), or **nil** when
  unset — and nil is a setting rather than a default: with it unset the engine installs
  no backend at all, leaving whatever the host application put in
  `taoensso.trove/*log-fn*` (`vaelii.impl.logging`).  So there is no default to name
  here, and `=verbose` is refused rather than read as the one there would have been."
  []
  (prop-enum "VAELII_LOG_LEVEL" log-level-spellings nil
             "error, warn, info, debug or trace"))

(defn max-query-ms
  "The wall-clock ceiling the daemon holds every bounded read to
  (`VAELII_MAX_QUERY_MS`, default 30000; 0 lifts it).  A request may name a smaller
  `:max-ms` and is refused for naming a larger one (`vaelii.host.serve`).

  **30 seconds because that is when the caller stops listening.**  The zero-dep client's
  own read timeout is 30 s (`vaelii.host.client`), and every op runs under the daemon's
  single write monitor — so a read still going after that is holding every other
  caller's request behind an answer nobody is waiting for."
  []
  (prop-long "VAELII_MAX_QUERY_MS" 30000 0 nil))

(defn max-query-depth
  "The rule-expansion ceiling the daemon holds every bounded read to
  (`VAELII_MAX_QUERY_DEPTH`, default 256; 0 lifts it).  A request may name a smaller
  `:max-depth` and is refused for naming a larger one (`vaelii.host.serve`).

  256 because it is the largest depth the API's own defaults name — `why`'s — so every
  documented call sits inside it, and a depth past it is a search a remote caller sized
  rather than the engine."
  []
  (prop-long "VAELII_MAX_QUERY_DEPTH" 256 0 nil))

(defn classify-max-cluster-members
  "The most members a coupled dilemma cluster may hold for the solve-free classifier to
  enumerate its optimal resolutions (`VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS`, default 12).
  A larger cluster is left `:supportable` — sound, since `:supportable` claims neither
  forced nor excluded — and a backend is the tool for a large interacting set.  Read per
  classification by `vaelii.impl.asp.label/classify-local`, which enumerates resolutions
  from the JTMS and never calls a solver: the `asp` in that namespace names the
  contradiction-solving subsystem, not clingo."
  []
  (prop-long "VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS" 12 1 nil))

(defn classify-resolution-budget
  "The number of candidate subsets one cluster's minimum-resolution enumeration may examine
  before the solve-free classifier abandons the cluster to `:supportable`
  (`VAELII_CLASSIFY_RESOLUTION_BUDGET`, default 20000).  A cluster of `m` members has
  2^m - 1 candidate subsets, so under the default member cap of 12 (at most 4,095) the
  budget binds only once `VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS` is raised above 14.  A
  per-read search bound, nothing retained.  Read per classification by
  `vaelii.impl.asp.label/classify-local`."
  []
  (prop-long "VAELII_CLASSIFY_RESOLUTION_BUDGET" 20000 1 nil))

(defn classify-max-joint-optima
  "The cap on the product of optima a cross-cluster datum's classification enumerates —
  the clusters that move the datum, times their optima
  (`VAELII_CLASSIFY_MAX_JOINT_OPTIMA`, default 1024).  A datum whose product is larger is
  left `:supportable`, since its class needs joint resolutions a backend enumerates.
  Read per classification by `vaelii.impl.asp.label/classify-local`."
  []
  (prop-long "VAELII_CLASSIFY_MAX_JOINT_OPTIMA" 1024 1 nil))

;; ---- the roster ---------------------------------------------------------

(def read-at-kinds
  "Where a switch's value is read **besides** `check!` — closed, because an open set of
  keywords would be a roster again, with the same drift and none of the checking.

  - `:open`   an entry point a caller is standing at: a store or log open, the daemon's start, a
              request.  A wrong value already stops that call and names itself, so
              `check!` moves an existing refusal earlier rather than inventing one.
  - `:load`   the root value of a var in another namespace, read at *that* namespace's
              load.  `check!` is not its first reader and cannot be — a var root cannot be
              deferred — so the refusal lands at load, naming the switch.
  - `:worker` read again after the open: on the fsync tick, per write, per solve.  A throw
              there is swallowed by a `catch Throwable` that logs a class name, or repeats
              every three seconds with the feature silently dead.  **These are the rows
              `check!` exists for.**"
  #{:open :load :worker})

(def switches
  "Every switch this namespace reads, one row per reader: `:names` — the spellings it
  reads, in the order it reads them — `:reader`, and `:read-at` from `read-at-kinds`.

  **One roster, not two.**  An accessor per switch and a hand-written call per switch in
  `check!` are the same set spelled twice, and nothing notices a reader that reaches one
  spelling and not the other.  What that leaves is this namespace's own failure — a
  process that reports itself configured and is not — on the properties that decide
  whether a crash loses data.  So `check!` walks this table, and `check-switches!` refuses
  a reader without a row at load.

  `:read-at` carries as a column what the ns docstring's *Where a refusal lands* section
  says about each row.  Prose naming switches by hand is a roster too, and one nothing can
  check."
  [{:names ["vaelii.disk.auto-compact"]             :reader #'disk-auto-compact?           :read-at :worker}
   {:names ["vaelii.disk.fsync"]                    :reader #'disk-fsync-mode              :read-at :open}
   {:names ["vaelii.disk.compress"]                 :reader #'disk-compress                :read-at :worker}
   {:names ["vaelii.disk.tokens"]                   :reader #'disk-tokens?                 :read-at :open}
   {:names ["vaelii.disk.cache"]                    :reader #'disk-cache-capacity          :read-at :open}
   {:names ["vaelii.disk.sync-ms"]                  :reader #'disk-sync-ms                 :read-at :open}
   {:names ["vaelii.disk.compact-dead-ratio"]       :reader #'disk-compact-dead-ratio      :read-at :worker}
   {:names ["vaelii.disk.compact-min-interval-ms"]  :reader #'disk-compact-min-interval-ms :read-at :worker}
   {:names ["vaelii.disk.lock"]                     :reader #'disk-lock?                   :read-at :open}
   {:names ["vaelii.index.snapshot"]                :reader #'index-snapshot?              :read-at :open}
   {:names ["vaelii.index.snapshot-drift"]          :reader #'index-snapshot-drift         :read-at :worker}
   {:names ["vaelii.belief.snapshot"]               :reader #'belief-snapshot?             :read-at :open}
   {:names ["VAELII_ARBITRATE_CONSTRAINTS"]         :reader #'arbitrate-constraints?       :read-at :load}
   {:names ["VAELII_ASSERTIVE_ARG_TYPES"]           :reader #'assertive-arg-types?         :read-at :load}
   {:names ["VAELII_CACHE_SCALE"]                   :reader #'cache-scale                  :read-at :load}
   {:names ["VAELII_PRUNE_SUBSUMED_MINTS"]          :reader #'prune-subsumed-mints?        :read-at :load}
   {:names ["VAELII_DEV"]                           :reader #'web-dev?                     :read-at :load}
   {:names ["VAELII_PROFILER"]                      :reader #'profiler?                    :read-at :open}
   {:names ["VAELII_PROFILER_PORT"]                 :reader #'profiler-port                :read-at :open}
   {:names ["VAELII_LOG_LEVEL"]                     :reader #'log-level                    :read-at :load}
   ;; the property is read first and the environment variable second, which is the order
   ;; `asp-solver` reads them in and the order the refusal has to name them in
   {:names ["vaelii.asp.solver" "VAELII_ASP_SOLVER"] :reader #'asp-solver                  :read-at :worker}
   {:names ["VAELII_CLINGO_MAX_BYTES"]              :reader #'clingo-max-program-bytes     :read-at :worker}
   {:names ["VAELII_ASP_TIME_LIMIT"]                :reader #'asp-time-limit               :read-at :worker}
   {:names ["VAELII_MAX_QUERY_MS"]                  :reader #'max-query-ms                 :read-at :open}
   {:names ["VAELII_MAX_QUERY_DEPTH"]               :reader #'max-query-depth              :read-at :open}
   {:names ["VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS"] :reader #'classify-max-cluster-members :read-at :worker}
   {:names ["VAELII_CLASSIFY_RESOLUTION_BUDGET"]   :reader #'classify-resolution-budget   :read-at :worker}
   {:names ["VAELII_CLASSIFY_MAX_JOINT_OPTIMA"]    :reader #'classify-max-joint-optima    :read-at :worker}])

(def switch-names
  "Every spelling on the roster, sorted.  `opts/check!`'s promise at the process entry point: a
  caller who can ask whether a name is one the build reads does not have to find out from
  a run that ignored it.  `config_surface_test` holds it to the names the sources
  actually name, so a row cannot claim a switch nothing reads."
  (into (sorted-set) (mapcat :names) switches))

(defn check!
  "Read every switch once, refusing the first whose value is outside its domain.
  `kb/open-kb` calls it, which is the earliest entry point that exists for the properties the
  durability daemon would otherwise read on a tick.

  Every switch and not this KB's: a `:memory` KB with `vaelii.disk.fsync=always` set is
  a process one directory away from a durability guarantee it does not have, and the
  next open is not a better place to hear about it.

  A walk of `switches` rather than a list of calls, so the set it reads is the set the
  roster declares and cannot be a subset of it."
  []
  (doseq [{:keys [reader]} switches] (reader))
  nil)

(def ^:private not-a-switch-reader
  "Public vars here that read no switch of their own, each with why.  A recorded
  exception rather than a suppression — `check-switches!` refuses one that has stopped
  being true, so an entry cannot outlive its reason, and refuses a blank one, since an
  exception with no reason is a suppression spelled longer.

  **Every** public var and not only the zero-arity functions.  The domain-carrying
  readers are all `defn`s today, but a switch read at the *root* of a `def` is a switch
  `check!` never calls and a scan keyed on `:arglists` cannot see — the one shape of the
  defect this table exists to refuse that the old scan admitted.  So the price of the
  wider net is these rows: the helpers, which read a switch their **caller** names, and
  the vocabularies and the roster itself, which read none."
  {'check!              "the walk over the roster, not a row in it"
   'prop-bool           "a helper: the switch it reads is the one its caller names"
   'prop-double         "a helper, as `prop-bool`"
   'prop-enum           "a helper, as `prop-bool`"
   'prop-long           "a helper, as `prop-bool`"
   'truthy              "the vocabulary every boolean switch is read against, not a read"
   'falsy               "the same, for off"
   'log-level-spellings "the vocabulary `log-level` is read against"
   'asp-solver-spellings "the vocabulary `asp-solver` is read against"
   'read-at-kinds       "the vocabulary a row's `:read-at` column is held to"
   'switches            "the roster itself"
   'switch-names        "the roster's spellings, derived from it"})

(defn- check-switches!
  "Refuse at load a reader with no row, an exemption that has gone stale or lost its
  reason, a name claimed by two rows, or a `:read-at` outside `read-at-kinds`.

  The first is the one that matters: a reader whose row nobody writes is a switch `check!`
  does not call, first read wherever it is used — which for a `:worker` row is a `catch
  Throwable` logging a class name on a three-second timer.  Every public var here is a
  switch reader unless `not-a-switch-reader` says otherwise, so a new one has to be given
  a row or named as the exception, and either is a decision somebody made rather than a
  line nobody wrote.

  **Takes its three tables**, rather than reading the vars beside it, so the refusals can
  be driven over a broken roster by a test.  A validator whose only caller is its own
  namespace's load has run every branch it will ever run against one table that passes:
  nothing then says it would refuse, and a `remove` written the wrong way round reads
  exactly like a table with nothing wrong.  `publics` is the symbol set the load hands it
  — this namespace's, since the call is the last form in the file.

  Refuses under `:bad-table-entry`, discriminated by `:mismatch`, as
  `predicates/check-families` does and for its reason: whichever way the table is bad, the
  caller catching it is the namespace load, and there is nothing a keyword of its own
  would let that caller do."
  [switches not-a-switch-reader publics]
  (let [rostered   (into #{} (map (comp :name meta :reader)) switches)
        exempt     (set (keys not-a-switch-reader))]
    (doseq [sym (sort (remove (into rostered exempt) publics))]
      (throw (ex-info (str "vaelii.impl.config/" sym " has no row on `switches`, so"
                           " `check!` does not call it and its value is first read at the"
                           " call site — for a worker read, inside a `catch Throwable`"
                           " that logs a class name.  Give it a row, or name it in"
                           " `not-a-switch-reader` with why it reads no switch.")
                      {:type :bad-table-entry :mismatch :unrostered-reader :reader sym})))
    (doseq [sym (sort (remove publics exempt))]
      (throw (ex-info (str "`not-a-switch-reader` names " sym ", which is not a public"
                           " var here — the exemption has outlived what it"
                           " excused.  Drop the entry.")
                      {:type :bad-table-entry :mismatch :stale-exemption :reader sym})))
    (doseq [sym (sort (filter rostered exempt))]
      (throw (ex-info (str sym " is both on `switches` and in `not-a-switch-reader` — one"
                           " of the two is wrong about whether it reads a switch.")
                      {:type :bad-table-entry :mismatch :exempt-and-rostered :reader sym})))
    (doseq [[sym why] (sort-by key not-a-switch-reader)
            :when     (not (and (string? why) (seq why)))]
      (throw (ex-info (str "`not-a-switch-reader` excuses " sym " and gives no reason — an"
                           " exception with no reason is a suppression, and the next reader"
                           " cannot tell an argument from an omission.")
                      {:type :bad-table-entry :mismatch :blank-exemption :reader sym}))))
  (doseq [{:keys [names reader read-at]} switches]
    (when-not (seq names)
      (throw (ex-info (str "switch row for " (:name (meta reader)) " names no switch —"
                           " `check!` would call it and `switch-names` would not list it,"
                           " so the surface would be short by one.")
                      {:type :bad-table-entry :mismatch :no-names
                       :reader (:name (meta reader))})))
    (when-not (read-at-kinds read-at)
      (throw (ex-info (str "switch row for " (:name (meta reader)) " reads at "
                           (pr-str read-at) ", which is not one of "
                           (pr-str (vec (sort read-at-kinds))) " — an entry point outside the"
                           " vocabulary is an entry point nothing can be said about.")
                      {:type :bad-table-entry :mismatch :read-at
                       :reader (:name (meta reader)) :read-at read-at}))))
  (doseq [[nm rows] (group-by identity (mapcat :names switches))
          :when     (< 1 (count rows))]
    (throw (ex-info (str nm " is claimed by " (count rows) " rows — two readers with two"
                         " domains for one name is one of them wrong, and which one wins"
                         " is the order `check!` happens to walk in.")
                    {:type :bad-table-entry :mismatch :duplicate-name :switch nm :property nm})))
  switches)

;; At load, as `predicates/check-families` runs at its own: a reader added without a row
;; is a build failure rather than a switch discovered to be unchecked by the crash it was
;; set to prevent.  The last form in the file, because `ns-publics` answers what has been
;; defined so far and a reader defined below this line would not be in it.
(check-switches! switches not-a-switch-reader
                 (set (keys (ns-publics 'vaelii.impl.config))))
