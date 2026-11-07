;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.chain
  "Forward chaining: the semi-naive fixpoint, one agenda for bare and defeasible
  rules alike, with the definitional checks re-run on the derivation path and the
  `exceptWhen` guard consulted before a conclusion is placed.

  Fifth layer of the engine stack (kb <- checks <- special <- integrate <- chain
  <- settle): a firing joins antecedents against stored facts (kb), checks its
  conclusion (checks), and reflects what it places into the caches through the
  derivation-path choke point (special).  Belief settling happens *after* a run,
  in `vaelii.impl.settle` — nothing here defeats or arbitrates."
  (:require [clojure.walk :as walk]
            [taoensso.trove :as trove]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.membership :as membership]
            [vaelii.impl.decide.negation :as negation]
            [vaelii.impl.decide.related :as related]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.except :as exc]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.quasiquote :as quasiquote]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.skolem :as skolem]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]
            [vaelii.impl.wiring :as wiring]))

(def default-chain-opts
  "The bounds a chaining run takes when `opts` names none.  `:max-term-depth` is the
  termination bound for term-building recursion: a firing whose conclusion nests terms
  deeper than it, and deeper than every term the firing rests on, is not placed
  (`term-cut?`).  `:max-derivations`, a cap on the conclusions and minted writes one run
  makes, and `:max-depth`, a bound on derivation depth, have no default
  (docs/inference.md, \"Forward chaining\")."
  {:max-term-depth 8})

(def ^:private default-progress-ms
  "How long a run may go without reporting, unless `opts` says otherwise
  (`:progress-every-ms`).  The interval is **wall-clock rather than a datum count**,
  because the two are not proportional: most datums are a fact triggering nothing and cost
  microseconds, while one rule datum joins over the whole corpus and can hold the loop for
  a minute on its own.  Counting datums would report thousands of times a second through
  the cheap stretch and go silent through the expensive one — which is the stretch a
  reader is watching."
  250)

(def ^:private ^:dynamic *tick*
  "Called by `derive-conclusion` after each rule firing with how many sentexes it created,
  or nil outside a reporting run.  This is what makes a *single* long datum visible: the
  agenda loop only sees a datum once it is finished, and the rule datum that fires over a
  whole corpus is one datum.  Bound by `chain` for the length of the run."
  nil)

(def ^:dynamic *stop*
  "The caller's bound on the runs under way (`call-with-stop`), or nil.  Every run reads
  the bound in force, so a settle's re-chain inside the bounded call stops with the run
  before it.  Read at the agenda loop, before each firing (`derive-conclusion`) and
  before each row of every join that enumerates firings (`planned-join`); never by a
  join that tests a condition (`solve-rule`), so a stop ends what a run generates and
  changes no answer a placement reads."
  nil)

(def ^:private ^:dynamic *bounds*
  "The chain bounds of the call under way (`call-with-stop`): `:max-depth`,
  `:max-term-depth` and `:max-derivations` from its `opts`, or nil.  A run takes each
  bound its own `opts` does not name from here."
  nil)

(defn- stop-of
  "The bound `opts` sets with `:max-ms` and `:stop?`, inside `enclosing`, or `enclosing`
  when `opts` sets neither.  `:stop?` is asked at most every `:progress-every-ms`."
  [opts enclosing]
  (let [{:keys [max-ms stop? progress-every-ms]} opts]
    (if (or max-ms stop?)
      {:deadline (when max-ms (budget/deadline {:max-ms max-ms}))
       :stop?    stop?
       :every    (* (long (or progress-every-ms default-progress-ms)) 1000000)
       :next     (volatile! (long (budget/now)))
       :hit      (volatile! false)
       :outer    enclosing}
      enclosing)))

(defn- stopped?
  "Has the bound `s` (a `stop-of` value, or nil for none) been reached?  Once it has, it
  stays reached.  The clock is read only when `s` sets `:max-ms` or `:stop?`."
  [s]
  (boolean
   (when s
     (or @(:hit s)
         (let [dl  (:deadline s)
               now (if (or dl (:stop? s)) (long (budget/now)) 0)]
           (when (or (when dl (>= now (long dl)))
                     (when-let [f (:stop? s)]
                       (when (>= now (long @(:next s)))
                         (vreset! (:next s) (+ now (long (:every s))))
                         (f)))
                     (stopped? (:outer s)))
             (vreset! (:hit s) true)))))))

(defn call-with-stop
  "`(f)` with the bound `opts` sets (`:max-ms`, a wall-clock bound in milliseconds from
  now, and `:stop?`, a function of no arguments whose truthy answer ends the run) in force
  for every run `f` starts, nested runs included (`*stop*`).  A run that reaches it inside
  `*rollback-scope*` throws `:interrupted`, unless `*keep-on-stop*` is set; outside one, or
  with it set, the run returns `:truncated?` with what it placed kept.  `opts` setting
  neither leaves the bound in force as it is.  The chain bounds `opts` names (`:max-depth`,
  `:max-term-depth`, `:max-derivations`) reach the same runs (`*bounds*`)."
  [opts f]
  (binding [*stop*   (stop-of opts *stop*)
            *bounds* (cond-> *bounds*
                       (map? opts) (merge (select-keys opts [:max-depth :max-term-depth
                                                             :max-derivations])))]
    (f)))

(def ^:dynamic *rollback-scope*
  "True inside a write whose throw rolls the store back to where the write found it
  (`core/undoing-refusal`, `edit!`'s adds).  A run there that its caller's bound ends,
  `:max-ms`, `:stop?` or `:max-derivations`, throws `:interrupted` (docs/inference.md,
  \"Stopping a run\").  The heap mark throws only here (`heap-check!`)."
  false)

(def ^:dynamic *keep-on-stop*
  "True inside a `forward-chain` called with `:on-stop :keep`: a run there that its
  caller's bound ends returns `:truncated?` and keeps what it placed, inside
  `*rollback-scope*` as outside it.  The heap mark throws all the same (`heap-check!`)."
  false)

(defn call-unbounded
  "`(f)` with no bound in force and outside `*rollback-scope*`, so no run `f` starts is
  stopped or interrupted (docs/inference.md, \"Stopping a run\").  The call's
  `:max-depth` and `:max-term-depth` stay in force."
  [f]
  (binding [*stop* nil *rollback-scope* false *bounds* (dissoc *bounds* :max-derivations)]
    (f)))

(defn interrupted!
  "Throw the refusal a run ends with when `bound` ended it: the caller's `:max-ms`,
  `:stop?`, `:max-derivations` or `:on-progress` (whose throw is `cause`), or `:heap`, an
  old generation the memory guard read as nearly full (`caches/heap-critical?`)."
  ([bound] (interrupted! bound nil))
  ([bound cause]
   (throw (ex-info (if (= :heap bound)
                     (str "the heap's old generation is nearly full, so this chaining run"
                          " stopped before it could exhaust it")
                     (str "the caller's " bound " ended this chaining run"))
                   {:type :interrupted :bound bound}
                   cause))))

(defn- heap-stop?
  "Does the heap mark stop a write here?  Over a nearly full heap (`caches/heap-critical?`)
  it does, except during a replay (`oplog/*replaying?*`), which runs each logged write to
  its end, as the logged write ran."
  []
  (and (not oplog/*replaying?*) (caches/heap-critical?)))

(defn- heap-check!
  "Throw `:interrupted :bound :heap` inside `*rollback-scope*` when the heap mark stops a
  write (`heap-stop?`), so the write rolls back.  Outside a rollback scope nothing would
  take back a run's partial writes, so the run goes on."
  []
  (when (and *rollback-scope* (heap-stop?)) (interrupted! :heap)))

(defn stop-reached?
  "Has the bound in force (`*stop*`) been reached?"
  []
  (boolean (some-> *stop* :hit deref)))

(defn- stop-bound
  "Which bound of `s` or of a bound it is nested in was reached: `:max-ms` when a deadline
  has passed, `:stop?` otherwise."
  [s]
  (let [now (long (budget/now))]
    (if (some #(some-> (:deadline %) (<= now)) (take-while some? (iterate :outer s)))
      :max-ms
      :stop?)))

(defn check-stop!
  "Throw `:interrupted` when the bound in force (`*stop*`) is reached or the heap mark
  stops a write (`heap-stop?`).  A write that runs no chain calls it between its writes
  (`core/bulk-assert-facts!`)."
  []
  (cond (heap-stop?)            (interrupted! :heap)
        (stopped? *stop*)       (interrupted! (stop-bound *stop*))))

(defn- cut
  "`states` up to the first one pulled after the bound `s` is reached; `states` itself when
  `s` is nil.  Under a bound, pulling a state runs `heap-check!`."
  [s states]
  (if s
    (take-while (fn [_] (heap-check!) (not (stopped? s))) states)
    states))

(def ^:private ^:dynamic *term-bound*
  "The running chain's term-nesting bound, or nil outside a run and under no bound:
  `{:max n :cut (volatile! 0)}`.  `:cut` counts the firings `term-cut?` refused."
  nil)

(def ^:private ^:dynamic *run-queue*
  "The running chain's queue for the seeds of a write one of its firings makes, or nil
  outside a run: `{:records r :seeds (volatile! [])}`.  A firing that mints a term (a
  reifiable NAT's constant, a skolem witness) asserts the mint's sentences, and each of
  those asserts hands its seeds to `chain-all`, which queues them here rather than
  starting a run inside the firing.  `chain` takes them onto its agenda after the datum,
  so the mint's consequences join the run that made it: one run and one set of bounds
  for every firing, and a chain of mints grows the agenda rather than the stack."
  nil)

(def ^:dynamic *matcher*
  "How the forward join looks up the stored facts satisfying a non-trigger antecedent:
  `(fn [kb pattern context] -> seq of [handle bindings …])`, returning exactly what
  `res/match-pattern` does.  The default is `res/match-pattern`; `vaelii.impl.rete` binds
  it to an alpha-memory matcher that answers the same set.  With the reference bound, a
  substituted antecedent with a bound indexable argument and a functor with sub-predicates
  is read through `res/matches-hierarchical` (`join-matches`); binding this var to anything
  else switches that off.  See docs/inference.md, \"Incremental rule matching\"."
  res/match-pattern)

(def ^:dynamic *suppress-duplicate-firings*
  "Whether a run generates each satisfying antecedent combination **once** rather than
  once per side that can trigger it (see `*agenda-arrivals*`).  On by default; bound
  **false** to enumerate every trigger, which is the reference side the oracles compare
  against (`witness_order_test`, `rete_oracle_test`).  A pure cost decision: the
  suppressed firings are duplicates of ones the run makes anyway, so the derived set
  and its supports are the same either way."
  true)

(def ^:dynamic *agenda-arrivals*
  "A mutable `{handle -> arrival}` map, the position at which each datum joined this
  run's agenda, or nil, and then nothing is suppressed.  It decides work, not belief: when
  two triggers of a rule enumerate the same pair, the later arrival skips the join
  (`arrival-admit`, `rule-arrival-admit`, `fire-rules-for`), and no tie-break keys on it.
  Keyed on arrival and not handle, since a datum put back on the agenda has an old handle
  and a fresh arrival.  A handle the run never enqueued has no arrival and is never
  suppressed against; a disbelieved trigger declines the filter.  Bound by `chain` for the
  length of a run.  A `java.util.HashMap`, since the engine is single-writer.  See
  docs/inference.md, \"What a run pays per witness\"."
  nil)

;; ---- exceptWhen: evaluating the exception -------------------------------
;; The exception is any closed level-6 query once the rule's bindings are substituted in:
;; the prover stack without rule backchaining (docs/exceptions.md, "The exception is a
;; query, not a literal").

(defn exception-holds?
  "Does `except`, a rule's exception as a vector of literals, hold under `bindings`,
  evaluated in `pctx`, the context the conclusion would be placed in?  An empty exception
  never holds, and an unanswerable one does not hold.  `provers/exception-holds?` answers,
  which the backward chainers call with the query's context."
  [kb except bindings pctx]
  (provers/exception-holds? kb except bindings pctx))

;; ---- negation-as-failure antecedents ------------------------------------
;; Read as block conditions beside the exception (`block-conditions`).  See docs/naf.md,
;; "In a rule antecedent".

(defn different-blocks?
  "Is a firing placed in `pctx` blocked because one of its `(different …)` antecedents
  does not hold there under the settled `bindings`?  Block-if-**any**, as an `unknown`
  is.  The join withholds a `different` literal (`join-order`) and `refusal-reason` asks
  this at each placement, so a merge `pctx` cannot see blocks nothing here; a reader below
  `pctx` that sees one reads a guard defeat instead (`different-guard-placements`,
  docs/predall.md, \"A `different` guard is re-checked, not supported\")."
  [kb different-antes bindings pctx]
  (boolean
   (some #(empty? (provers/solve-goal kb (res/substitute % bindings) pctx))
         different-antes)))

(defn closed-extent-antecedents
  "`rules/closed-extent-antecedents` over this KB's taxonomy: the negative antecedents
  the join withholds and derive time decides."
  [kb antes]
  (rules/closed-extent-antecedents (reasoning/taxonomy kb) antes))

(defn closed-extent-blocks?
  "Is a firing blocked because one of its withheld negative antecedents `ce-antes` does
  not hold under `bindings` in `pctx`, asked as the whole level-6 question (docs/naf.md,
  \"Under the grant, a negative antecedent is NAF\")?"
  [kb ce-antes bindings pctx]
  (boolean (some #(not (provers/exception-holds? kb [%] bindings pctx)) ce-antes)))

(defn redecided-negative-antecedents
  "The closed negative antecedents of the stored rule `rsx` a re-decision of its firings
  asks as the level-6 question (`closed-extent-blocks?`): those `closed-extent-antecedents`
  selects, and those on a predicate the re-check index posts the rule under.  The second
  set holds the literals a firing made under a since-retracted grant withheld from the
  join: the firing holds no support handle for one, and `special/index-closed-extent-rules`
  leaves the posting in place when the grant leaves.  `[]` with no negative antecedent."
  [kb rsx]
  (let [antes (:antecedent rsx)]
    (if-not (some rules/negative-literal? antes)
      []
      (let [tx  (reasoning/taxonomy kb)
            idx (:index kb)]
        (filterv #(let [p (nm/functor (second %))]
                    (or (rules/closed-extent-declared? tx p)
                        (reads/watched-rule-on? idx p (:id rsx))))
                 (rules/closed-negative-antecedents antes))))))

(defn- disagreeing-solutions
  "The disagreeing solutions of one post-join literal as a content-ordered vector of
  `[[?var value] …]`, for the ledger entry that names them.

  Ordered by content, never by the order the registry yielded them: an entry naming them
  in solution order would carry into the ledger the very arrival dependence the refusal
  exists to remove, so the same knowledge loaded either way would file two different
  entries about one defect and `report-once` would keep both."
  [sols]
  (nm/sort-by-content-key identity (mapv #(nm/sort-by-content-key first (mapv vec %)) sols)))

(defn post-join-bindings
  "Extend `bindings` with what a firing's post-join literals compute
  (`rules/post-join-literals`), solving each through the registry under the bindings the
  earlier ones produced: an aggregate or `different` in `pctx`, any other literal in the
  wildcard.  Nil is a block: a literal has no answer, its bound output no longer matches
  the recomputed value, or its solutions disagree (also filed as `:post-join-ambiguous`).
  At most two solutions are realized (docs/aggregate.md, \"Comparing the count\")."
  [kb literals bindings pctx]
  (reduce (fn [bs lit]
            (let [g    (res/substitute lit bs)
                  ctx  (if (or (sx/aggregate? lit) (= 'different (nm/functor lit))) pctx '?ctx)
                  sols (into [] (comp (distinct) (take 2)) (provers/solve-goal kb g ctx))]
              (case (count sols)
                1 (merge bs (first sols))
                0 (reduced nil)
                (do (violations/report-once
                     kb {:violation :post-join-ambiguous
                         :context   pctx
                         :detail    {:literal   g
                                     :solutions (disagreeing-solutions sols)
                                     ;; `print-key`, not `pr-str`: the message is deduped by `report-once`, and an ambient `*print-length*` would elide two literals to one string
                                     :message   (str "post-join literal " (nm/print-key g)
                                                     " has more than one solution; a firing "
                                                     "that took one of them would depend on "
                                                     "the order the facts arrived")}})
                    (reduced nil)))))
          bindings
          literals))

(defn- antecedent-calculi
  "The registered calculi the antecedents `antes` draw on."
  [kb antes]
  (into #{}
        (keep (fn [ante]
                (when (and (sequential? ante) (= 3 (count ante)) (symbol? (first ante)))
                  (qkb/calculus-for kb (first ante)))))
        antes))

(defn- rule-calculi
  "The registered calculi a rule's antecedents draw on."
  [kb rsx]
  (antecedent-calculi kb (:antecedent rsx)))

(defn- typed-antecedent-unadmitted?
  "Does a positive antecedent of `rsx` on a calculus's `:typed` predicate, under the
  firing's `bindings` (a delay), name an argument the declared types no longer admit at
  `pctx` (`qkb/typed-admits?`), with no believed stored fact stating it?  The admission
  reads the absence of a disjoint membership, which no support handle names, so a
  membership arriving withdraws the firing here (docs/qcn.md, \"Reading out\")."
  [kb rsx bindings pctx]
  (boolean
   (some (fn [a]
           (when-let [c (when (and (sequential? a) (= 3 (count a)) (symbol? (first a)))
                          (qkb/calculus-for kb (first a)))]
             (when (contains? (:typed c) (first a))
               (let [[p x y :as g] (res/substitute a @bindings)]
                 (and (not-any? #(and (symbol? %) (sx/variable? %)) [x y])
                      (not (qkb/typed-admits? c kb p x y pctx))
                      (not-any? #(jtms/in? (reasoning/tms kb) (first %))
                                (res/matches-visible kb g pctx)))))))
         (:antecedent rsx))))

(defn- antecedent-blocked?
  "Does one of the antecedents `antes` on a calculus predicate, under the firing's
  `bindings` (a delay), name a node of an unsatisfiable component of that calculus's
  network at `pctx` (`qkb/blocked-nodes`)?"
  [kb antes bindings pctx]
  (boolean
   (some (fn [a]
           (when-let [c (when (and (sequential? a) (= 3 (count a)) (symbol? (first a)))
                          (qkb/calculus-for kb (first a)))]
             (let [blocked (qkb/blocked-nodes c kb pctx)]
               (and (seq blocked)
                    (some blocked (rest (res/substitute a @bindings)))))))
         antes)))

(defn- entailment-withdrawn?
  "Does an antecedent this rule joins on a calculus name a node of an unsatisfiable
  component at `pctx` (`antecedent-blocked?`), or does a typed antecedent's answer no
  longer admit its arguments there (`typed-antecedent-unadmitted?`)?  The settle blocks
  such a firing as it blocks an excepted one (docs/qcn.md, \"An unsatisfiable network
  withdraws what it licensed\")."
  [kb rsx bindings pctx]
  (let [calcs (rule-calculi kb rsx)]
    (boolean (and (seq calcs)
                  (or (antecedent-blocked? kb (:antecedent rsx) bindings pctx)
                      (typed-antecedent-unadmitted? kb rsx bindings pctx))))))

(defn entailment-withdrawable?
  "Can `entailment-withdrawn?` answer true for any firing of the rule `rsx`, whatever
  context it was placed in?  True only while a calculus it joins on is unsatisfiable
  somewhere (`qkb/unsatisfiable-somewhere?`)."
  [kb rsx]
  (boolean (some #(qkb/unsatisfiable-somewhere? % kb) (rule-calculi kb rsx))))

(defn answered-by-calculus?
  "Does a registered calculus claim `pred` or a sub-predicate of it, by the global spec
  closure?"
  [kb pred]
  (boolean (and (symbol? pred)
                (some #(qkb/calculus-for kb %)
                      (tax/specs-global (reasoning/taxonomy kb) pred)))))

(def ^:dynamic *declarations-cell*
  "Per-run cache of `inherit/declarations-exist?`: a volatile holding the answer, or nil
  (unknown); the var is nil outside a chaining run.  Bound once by `chain` and reset by
  `derive-conclusion` when a placed conclusion roots at a declaration functor
  (`note-placed-declaration!`).  See docs/inference.md."
  nil)

(def ^:dynamic *computed-rejoins*
  "Per-run record of the computed re-joins owed and not yet run (`owe-computed-rejoins`):
  `{:owed m :queue q}`, `m` a `java.util.HashMap` from rule handle to the source datums
  that owed it since its marker was queued (`:all` when one cannot filter the join), `q`
  a volatile vector of the markers the agenda takes next.  Nil outside a run, where a
  source datum re-joins at once (docs/inference.md, \"What a computed answer rests
  on\")."
  nil)

(def ^:dynamic *batch-rejoins*
  "The re-joins a `with-deferred-settle` batch owes (`owe-computed-rejoins`), as a
  `java.util.HashMap` shaped as `*computed-rejoins*`' `:owed`, which the batch's closing
  settle runs (`run-batch-rejoins`).  Nil outside a batch."
  nil)

(def ^:dynamic *closure-rejoins*
  "Per-run record of the closure re-joins `fire-rules-for` has run, as a
  `java.util.HashMap` from rule handle to the `special/taxonomy-generations` value its
  full join read; nil outside a chaining run, where every closure edge re-joins in full.
  A rule whose recorded value has not moved fires at the datum's trigger position instead
  (docs/inference.md, \"An edge moving re-joins the rule\")."
  nil)

(defn- declarations-exist?
  "The run's cached answer when a run has bound one (reading the index once per
  invalidation), else `inherit/declarations-exist?` live."
  [kb]
  (if-let [v *declarations-cell*]
    (if-some [x @v]
      x
      (vreset! v (inherit/declarations-exist? kb)))
    (inherit/declarations-exist? kb)))

(defn- placed-functor
  "The functor a conclusion literal roots at **once it is placed**, which is not always
  the functor it is written with: a negation roots under its positive body's predicate
  (`kv/root-keys` — polarity lives in the record, so `(not (p a))` counts under `p` and
  never under `not`).  So `not` is never the answer here, and a conclusion wearing it
  would otherwise be read as a functor no declaration uses."
  [c]
  (when (sequential? c)
    (let [f (nm/functor c)]
      (if (= sx/not-functor f) (nm/functor (kb/body-under-not c)) f))))

(defn- note-placed-declaration!
  "A placed conclusion roots at a preservation declaration's functor: forget the run's
  cached answer to whether any exist, so the next join asks again.  Asked of every firing
  that reached placement, since a conclusion that dedups onto a stored sentex still places
  the justification that makes the declaration believed.  Only a cached false can go stale,
  so a run that has not answered, or answered yes, skips the scan."
  [conjuncts]
  (when-let [v *declarations-cell*]
    (when (and (false? @v)
               (some #(contains? inherit/declarations (placed-functor %)) conjuncts))
      (vreset! v nil))))

(defn- declaration-record?
  "Is the record `sxr` a preservation declaration (`inherit/declarations`): a handle a
  firing that joined on an inherited claim names among its antecedents?"
  [sxr]
  (let [s (:sentence sxr)]
    (boolean (and (sequential? s) (contains? inherit/declarations (nm/functor s))))))

(defn- preserving-antecedent?
  "Does `ante` name a predicate carrying a preserved argument position, visible from
  `context`?  False for every literal in a KB that declares no preservation, at the
  cost of the presence check in front of `inherit/positions` — read once per chaining run
  (`*declarations-cell*`, re-read after a derived declaration), so the per-antecedent
  cost there is a var deref and a symbol test.

  A negation is not one: the forward join reads claims on a positive antecedent alone
  (`inherit/ground-goal?`), and a negated one joins on stored denials."
  [kb ante context]
  (and (sequential? ante) (seq ante)
       (let [f (nm/functor ante)]
         (and (symbol? f) (not= 'not f) (seq (nm/args ante))
              (declarations-exist? kb)
              (boolean (seq (inherit/positions kb f context)))))))

(defn- inherited-goals
  "The ground goals the preserved antecedents of the rule `rsx` take under `bindings` (a
  delay) that the network does not state at `pctx`: the antecedents a firing joined on
  an inherited claim.  A stored claim is withdrawn by its own handle going, and asking
  `verdict` about one would block an ordinary firing over a pair the KB happens to hold in
  both polarities, which is a represented dilemma.  `bindings` is forced only once a
  preserved antecedent is found."
  [kb rsx bindings pctx]
  (let [as (filterv #(preserving-antecedent? kb % pctx) (:antecedent rsx))]
    (when (seq as)
      (binding [tax/*network-belief* true]
        (into []
              (comp (map #(res/substitute % @bindings))
                    (filter inherit/ground-goal?)
                    (filter (fn [g] (not-any? #(jtms/in? (reasoning/tms kb) (first %))
                                              (res/matches-visible kb g pctx)))))
              as)))))

(defn- inheritance-withdrawn?
  "Was this firing licensed by an inherited claim a `:monotonic` contrary claim undercuts
  in `pctx`?  The firing is blocked as an excepted one is.  A `:default` contrary is set
  aside (`inherit/*default-contraries-set-aside*`) and a defeat rests on it
  (`inheritance-defeat-placements`).  Claims are read in the network and through the
  excepts (`tax/*network-belief*`).  See docs/inherit.md."
  [kb rsx bindings pctx]
  (boolean
   (when-let [gs (seq (inherited-goals kb rsx bindings pctx))]
     (binding [tax/*network-belief*                  true
               inherit/*memo*                        nil
               inherit/*default-contraries-set-aside* true
               inherit/*concluding*                  (nm/functor (:consequent rsx))]
       (some #(not= :for (inherit/verdict kb % pctx)) gs)))))

(defn- post-join-withdrawn?
  "Was this firing licensed by a count the KB no longer computes?  Re-runs the rule's
  post-join literals in `pctx` under the firing's stored `bindings`, where every output
  is bound, so each runs in check mode (docs/aggregate.md, \"Maintenance\").
  `bindings` is a delay, forced only when the rule has a post-join literal."
  [kb rsx bindings pctx]
  (let [post (rules/post-join-antecedents rsx)]
    (boolean (and (seq post)
                  (nil? (post-join-bindings kb post @bindings pctx))))))

(defn- settled-bindings
  "A firing's stored bindings with each bound term rewritten to the normal form `pctx`
  now elects (docs/equality.md, \"What a merge does\" step 4).  A justification records
  what matched when it fired, so a re-check that substituted the stored bindings would ask
  under a retired spelling and read an empty answer as *not excepted*.  One visibility
  predicate for the whole map; the bindings come back unchanged when the partition is
  empty and no schematic equation is declared."
  [kb bindings pctx]
  (let [tx (reasoning/taxonomy kb)]
    (if (and (nil? (tax/merged-term-pred tx)) (empty? (tax/rewrite-rules tx)))
      bindings
      (let [visible? (res/visible-supporter-fn kb pctx)]
        (reduce-kv (fn [m v t] (assoc m v (kb/rewrite-term* kb t visible?))) {} bindings)))))

(defn- antecedent-hidden?
  "Does a believed visibility `except` hide one of `antes` from `pctx`: name it, or name a
  handle every justification route of it rests on (`exc/except-closure-hidden-fn`)?  The
  rule handle among `antes` is asked too.  Asked per antecedent; a nil predicate is the
  presence check."
  [kb antes pctx]
  (if-let [hidden? (exc/except-closure-hidden-fn kb pctx)]
    (boolean (some hidden? antes))
    false))

(defn- mention-read
  "The positive literals of `antes`, substituted under `b`, holding a compound at a
  position a stored declaration makes a mention (`res/mention-declarations`), which a
  reader may read in another order than the store holds it, each with `pred`'s answer."
  [kb antes b pred]
  (let [tax (reasoning/taxonomy kb)]
    (keep (fn [a] (when (and (seq? a) (or (sx/variable? (first a)) (res/declares-mention? tax (first a))))
                    (let [g (res/substitute a b)]
                      (when (and (seq? g) (symbol? (first g)) (not (sx/variable? (first g)))
                                 (res/declares-mention? tax (first g))
                                 (not= sx/not-functor (first g)) (not (sx/unknown? g)) (not (sx/aggregate? g))
                                 (some (fn [n] (let [t (nth g n)]
                                                 (and (seq? t) (seq t) (seq (res/mention-declarations kb tax (first g) n)))))
                                       (range 1 (count g))))
                        [g (pred g)]))))
          antes)))

(defn- probed-only?
  "Does a believed fact visible at `pctx` hold the literal `g` with a compound at a
  mention in another order (`sx/mention-arrangements`), and none hold `g` in the store's
  own spelling (`res/matches-visible*`), so a join matched `g` through a mention probe?"
  [kb g pctx]
  (let [tms (reasoning/tms kb)
        in? (fn [s] (some (fn [[h]] (jtms/in? tms h)) (res/matches-visible* kb s pctx)))]
    (and (not (in? g))
         (boolean (some in? (rest (sx/mention-arrangements g (res/store-marks kb) (constantly true))))))))

(defn- mention-unread?
  "Does a reader at `pctx` find no believed match (`res/matches-visible`) for one of
  `antes` under `b` that only a mention probe matches (`probed-only?`): the reader reads
  the mention, so the stored order is not the antecedent's?"
  [kb antes b pctx]
  (let [tms (reasoning/tms kb)]
    (boolean (some (fn [[_ none?]] none?)
                   (mention-read kb antes b
                                 #(and (probed-only? kb % pctx)
                                       (not-any? (fn [[h]] (jtms/in? tms h)) (res/matches-visible kb % pctx))))))))

;; ---- forward chaining ---------------------------------------------------

;; **Deferred antecedents.**  A deferred (evaluable) literal (`lessThan`, `evaluate`,
;; `different`, a `sentex/deferred-predicates` member, or a registered `add-evaluatable`
;; predicate; `deferred-antecedent?`) is computed from the bindings the other antecedents
;; produced and is not a stored fact, so the join goes to the prover registry and not to
;; `match-pattern`.  A `different` literal is withheld by the join and decided per
;; placement (`join-order`, `different-blocks?`).  A registered evaluatable is per-KB, so
;; `planned-join` places it after its binders by cost
;; (`provers/evaluatable-est-override`).  See docs/inference.md, "Deferred antecedents in
;; a forward join".

(defn- solve-deferred
  "Solve a deferred antecedent against `bindings` by computing it: the substituted
  literal goes to the prover registry (`EvaluableProver`, `EvaluateProver`,
  `DifferentProver`, `QuantityProver`).  Returns `[bindings support]` pairs: a test yields
  the bindings unchanged or nothing, `evaluate` adds the binding it computed.  `support` is
  the handles the answer was read from (empty for arithmetic comparisons;
  `prover-types/SupportingProver` says which provers report some).  The context is the
  wildcard.  Throws when an input is unbound (`sentex/check-naf-closed` and `planned-join`
  prevent it), since an empty join would report a comparison never run as one that failed.
  See docs/inference.md, \"Deferred antecedents in a forward join\"."
  [kb literal bindings]
  (let [g (res/substitute literal bindings)]
    ;; The unbound-input guard covers the built-in deferred literals, whose input/output
    ;; split `sentex/deferred-input-vars` knows; a KB evaluatable's readiness is left to the
    ;; prover (`EvaluatableFn` yields nothing until its inputs are ground).
    (when (sx/deferred-literal? literal)
      (when-let [unbound (seq (sx/deferred-input-vars g))]
        (throw (ex-info (str "deferred antecedent " (pr-str g) " reached the join with unbound "
                             "input " (pr-str (vec unbound)) " — it is computed, not looked up, "
                             "so an earlier antecedent must bind its inputs")
                        {:type :unbound-deferred :literal literal :goal g :unbound (vec unbound)}))))
    (map (fn [[b sup]] [(merge bindings b) sup])
         (provers/solve-goal-with-support kb g '?ctx))))

;; ---- qualitative antecedents: joining on what a network entails ----------
;; An entailed antecedent contributes the handles its entailment rests on, beside the
;; ordinary match (docs/qcn.md).

(def ^:dynamic *qcn-contexts*
  "`{calculus-name -> #{context}}`, the reader contexts an entailed antecedent is solved
  against, memoized for one agenda datum (`process-datum`); nil outside one.  Per datum and
  not per run: a placed qualitative conclusion is a datum of its own whose re-join reads
  the contexts afresh."
  nil)

(defn- calculus-contexts
  "`qcn-kb/reader-contexts` of `calc`, through `*qcn-contexts*` when it is bound
  (docs/qcn.md, \"Which networks it joins against\")."
  [kb calc]
  (if-let [memo *qcn-contexts*]
    (or (get @memo (:name calc))
        (let [cs (qkb/reader-contexts kb calc)] (swap! memo assoc (:name calc) cs) cs))
    (qkb/reader-contexts kb calc)))

(def ^:dynamic *qualitative-delta*
  "`{:literal <antecedent> :moved {context (:all | #{pair})}}`, or nil.  Bound by
  `delta-fire-rule`: the antecedent equal to `:literal` enumerates only the moved pairs
  (`qcn-kb/join-delta`), every other one in full.  Keyed by literal, not position, since
  `plan/order` reorders the antecedents."
  nil)

(defn- solve-qualitative
  "Solve a qualitative antecedent by entailment at each reader context of `calc`, each
  solution's handles extended by the support it rests on (`qcn-kb/solve-with-support`).
  When `*qualitative-delta*` names this literal, each context enumerates its moved pairs,
  and a context with none is skipped."
  [kb calc literal states]
  (let [ctxs  (calculus-contexts kb calc)
        d     *qualitative-delta*
        moved (when (and d (= literal (:literal d))) (:moved d))]
    (distinct
     (for [{:keys [bindings handles matched]} states
           :let [g (res/substitute literal bindings)]
           ctx ctxs
           :let [m     (when moved (get moved ctx :all))
                 pairs (when (and m (not= m :all)) m)]
           :when (or (nil? m) (= m :all) (seq pairs))
           [bnd sup] (qkb/solve-with-support calc kb g ctx pairs)]
       ;; `:matched` passes through unextended: an entailed antecedent was licensed by
       ;; the network, and the `genl` edges a sub-predicate fact was read over are in
       ;; its support already (`qcn-kb/asserted-pairs`).
       {:bindings (merge bindings bnd) :handles (into handles sup) :matched matched}))))

(defn- qualitative-antecedent
  "The registered calculus claiming `ante` when it is a positive binary literal, or nil.
  A negated antecedent is matched only (docs/qcn.md, \"Forward chaining too\")."
  [kb ante]
  (when (and (sequential? ante) (= 3 (count ante)) (symbol? (first ante)))
    (qkb/calculus-for kb (first ante))))

;; ---- inherited antecedents: joining on a claim nobody stored -------------
;; `(transitiveInArg P n R)` makes a stored `(P … W …)` license `(P … A …)` for every A in
;; W's reach (docs/inherit.md).  `inherit/solve-with-support` answers the antecedent by the
;; reach and returns the handles the claim was read from (the stated claim, the
;; declaration, the reach edges), so the conclusion is withdrawn when any goes and is placed
;; only where all are seen.  The answers are unioned with the stored matches, and the
;; diagonal is dropped.

(defn- solve-preserving
  "Solve an antecedent by preservation, against the claims stored anywhere.  Each solution
  carries the handles the inherited claim rests on.  The context is `'?ctx` throughout.
  `cpred` is the rule's consequent predicate: a predicate the rule concludes on or below
  walks no self relation (`inherit/*concluding*`)."
  [kb literal states cpred]
  (let [ak (rules/antecedent-key literal)]
    (for [{:keys [bindings handles matched]} states
          :let [g (res/substitute literal bindings)]
          {b :bindings sup :handles claim :claim} (binding [inherit/*default-contraries-set-aside* true
                                                            inherit/*concluding*                  cpred]
                                                    (inherit/solve-with-support kb g '?ctx))]
      ;; the claim is paired with the antecedent's key so `subsumption-links` reads the edges
      ;; it rests on; the declaration and reach edges licensed the move and are not paired
      {:bindings (merge bindings b) :handles (into handles sup)
       :matched  (conj matched [ak claim])})))

;; ---- computed antecedents: joining on what a prover reads out of the store -----
;; A `SupportingProver` answers a goal from stored facts nothing about the goal names; it
;; reports the handles the answer was read from, so the firing rests on them and the
;; ordinary relabel withdraws it when any goes.  The read is per reader context
;; (`provers/source-contexts`), and the answers are unioned with the ordinary matcher's;
;; the TMS dedups the duplicate justification (docs/inference.md, "What a computed answer
;; rests on").

(defn- computed-antecedent?
  "Is `ante` a literal a registered `SupportingProver` answers — and therefore one the
  join solves by computation as well as by matching?

  Nil is close to free: `provers/support-answered-preds` memoizes against the registry's
  identity, so this is a set lookup on a functor.  It is not empty for the default
  registry — `QuantityProver` ships in it — so the check below is a `contains?` on the
  literal's own functor and stops there for every ordinary antecedent."
  [kb ante]
  (and (sequential? ante) (seq ante) (symbol? (first ante))
       (contains? (provers/support-answered-preds kb) (first ante))))

(defn- solve-computed
  "Solve an antecedent by computation over stored facts, at each reader context the
  prover's sources reach.  Each solution carries the handles the answer rested on.  An
  answer a `SupportingProver` gives with empty support joins, and `planned-join` drops a
  firing of such a rule when its combined handles are empty; an empty-support answer from
  any other prover is dropped (`provers/solve-goal-reporting-support`).  `:matched` passes
  through unextended.  `ctxs` default to the readers of the registry's declared sources
  (`provers/source-contexts`); a transitive antecedent passes its walk's
  (`transitive-contexts`), an expression kind and a `nonempty` goal add the contexts of the
  form's head or of a member (`provers/stated-kind-handles`, `provers/nonempty-contexts`)."
  ([kb literal states]
   (let [preds (provers/support-source-preds kb)
         f     (nm/functor literal)]
     (cond
       (contains? provers/expression-kind-predicates f)
       (distinct
        (mapcat (fn [st]
                  (solve-computed kb literal [st]
                                  (provers/source-contexts
                                   kb preds (provers/stated-kind-handles
                                             kb (res/substitute literal (:bindings st))))))
                states))
       (= 'nonempty f)
       (distinct
        (mapcat (fn [st]
                  (solve-computed kb literal [st]
                                  (or (provers/nonempty-contexts
                                       kb preds (res/substitute literal (:bindings st)))
                                      (provers/source-contexts kb preds))))
                states))
       :else
       (solve-computed kb literal states (provers/source-contexts kb preds)))))
  ([kb literal states ctxs]
   (distinct
    (for [{:keys [bindings handles matched]} states
          :let [g (res/substitute literal bindings)]
          ctx ctxs
          [bnd sup reported?] (provers/solve-goal-reporting-support kb g ctx)
          :when (or (seq sup) reported?)]
      {:bindings (merge bindings bnd) :handles (into handles sup) :matched matched}))))

(defn- computed-withdrawn?
  "Was this firing licensed by a computed answer the KB no longer computes?  Each
  antecedent `computed-antecedent?` claims is solved again in `pctx` under the firing's
  stored `bindings` (a delay) minus its outputs, the variables no other binding
  antecedent shares, and the firing is withdrawn when the answer it bound is not among
  the answers and no believed stored fact states it.  The post-join arm's
  twin for a joined literal: a tightest bound narrows as sources arrive, so the
  justification's handles all stay believed while the answer moves (docs/inference.md,
  \"What a computed answer rests on\")."
  [kb rsx bindings pctx]
  (let [antes (:antecedent rsx)]
    (when-let [cs (seq (filter #(computed-antecedent? kb %) antes))]
      (let [b   @bindings
            tms (reasoning/tms kb)]
        (boolean
         (some (fn [a]
                 (let [shared (into #{} (comp (remove #{a})
                                              (remove sx/deferred-literal?)
                                              (remove #(computed-antecedent? kb %))
                                              (mapcat sx/free-vars))
                                    antes)
                       outs   (remove shared (sx/free-vars a))
                       g      (res/substitute a (apply dissoc b outs))
                       want   (res/substitute a b)]
                   (and (not-any? #(= want (res/substitute g %)) (provers/solve-goal kb g pctx))
                        (not-any? #(jtms/in? tms (first %)) (res/matches-visible kb want pctx)))))
               cs))))))

(def ^:dynamic *lazy-rules*
  "Per-run cache of `lazy-table`: a volatile holding the table, or nil (unread); the var
  is nil outside a chaining run.  `process-datum` empties it when a lazy-forward rule
  arrives.  A forward join proves a literal a lazy-forward rule concludes by joining the
  rule's antecedents (docs/inference.md, \"A lazy-forward rule\")."
  nil)

(def ^:dynamic *lazy-solving*
  "The handles of the lazy-forward rules whose antecedents the join is proving: a rule is
  not offered to the join of its own antecedents."
  #{})

(def ^:dynamic *lazy-delta*
  "The source datum handles `planned-join` keeps rows of past its last computed or
  lazy-forward antecedent, bound while it joins that antecedent, else nil.  `solve-lazy`
  proves the literal from those datums alone for a state resting on none of them."
  nil)

(defn- offerable-lazy?
  "Can a forward join prove `rsx`'s conclusion by joining its antecedents?  Not when an
  antecedent is decided after the join (`unknown`, an aggregate, `different`, a
  closed-extent negation) or the rule carries an `exceptWhen`: the join reads neither."
  [kb rsx]
  (let [antes (:antecedent rsx)]
    (and (not-any? #(or (sx/unknown? %) (sx/aggregate? %) (= 'different (nm/functor %))) antes)
         (empty? (closed-extent-antecedents kb antes))
         (empty? (provers/rule-exceptions kb (:id rsx))))))

(defn- lazy-table
  "The stored lazy-forward rules a forward join can prove by (`offerable-lazy?`), as
  `{:by-functor {consequent-functor [rsx …]} :handles #{h …}}`, each group in content
  order; nil when the store holds none (`kb/stores-lazy-rule?`).  Read over every context:
  the firing's placement reads the lazy rule's context."
  [kb]
  (let [idx (:index kb)]
    (when (kb/stores-lazy-rule? kb)
      (let [rs (->> (reads/as-stored-rules-in-global idx :lazy)
                    (keep #(p/get-sentex (:records kb) %))
                    (filter #(and (rules/lazy-sentex? %) (offerable-lazy? kb %)))
                    (nm/sort-by-content-key (juxt sx/sentence-of :context)))]
        {:by-functor (group-by #(nm/functor (:consequent %)) rs)
         :handles    (into #{} (map :id) rs)}))))

(defn- lazy-rules
  "`lazy-table` through the run's cache (`*lazy-rules*`), or read live outside a run."
  [kb]
  (if-let [v *lazy-rules*]
    (let [t @v] (if (nil? t) (vreset! v (or (lazy-table kb) false)) t))
    (lazy-table kb)))

(defn- lazy-antecedent-rules
  "The lazy-forward rules a join of a rule concluding on `cpred` proves `ante` by, or nil:
  those concluding on `ante`'s own functor, believed and not being proved now
  (`*lazy-solving*`).  None when one of the rules concluding on that functor reads `cpred`
  itself: the joining rule is then the converse of that functor's lazy reading in every
  context, and its join takes the matcher alone, as `walks-its-own-conclusion?` rules for a
  walk.  A lazy rule reading a predicate above `cpred` is decided per placement context
  (`converse-lazy-reading?`).  Nil on a store holding no lazy-forward rule
  (`kb/stores-lazy-rule?`)."
  [kb ante cpred]
  (when (and (sequential? ante) (seq ante))
    (let [f (first ante)]
      (when (and (symbol? f) (not (sx/variable? f)) (not= sx/not-functor f))
        (when-let [rs (seq (get (:by-functor (lazy-rules kb)) f))]
          (when-not (some (fn [r] (some #(= cpred (placed-functor %)) (:antecedent r))) rs)
            (not-empty
             (filterv #(and (not (contains? *lazy-solving* (:id %))) (res/rule-believed? kb (:id %)))
                      rs))))))))

(defn- converse-lazy-reading?
  "Does a firing of a rule concluding on `cpred` over the antecedents `antes`, resting on
  the lazy-forward rule records `lazies`, prove a lazy literal by the converse of its
  reader's lazy reading in `pctx`: does a lazy rule read a predicate in `pctx`'s `genls` of
  what the rule proving through it concludes on, `cpred` for a lazy rule on a functor of
  `antes` and the consequent predicate for one another of `lazies` proves through?  Such a
  firing places nothing in `pctx` (`place-conseq`) and its justification is blocked there
  (`lazy-firing-blocked?`)."
  [kb cpred antes lazies pctx]
  (let [tx  (reasoning/taxonomy kb)
        fns (fn [as] (into #{} (keep placed-functor) as))]
    (boolean
     (some (fn [l]
             (let [f     (placed-functor (:consequent l))
                   reads (fns (:antecedent l))
                   by    (cond-> (into [] (comp (remove #{l})
                                                (filter #(contains? (fns (:antecedent %)) f))
                                                (map #(placed-functor (:consequent %))))
                                       lazies)
                           (contains? (fns antes) f) (conj cpred))]
               (some (fn [c] (when (symbol? c) (some #(contains? (tax/genls tx c pctx) %) reads))) by)))
           lazies))))

(defn- proves-lazily?
  "Does the join of the rule at `rh` prove an antecedent on `f` by a lazy-forward rule
  (`lazy-antecedent-rules`)?"
  [kb rh f]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (let [cpred (some-> (:consequent rsx) nm/functor)]
      (boolean (some #(and (sequential? %) (= f (first %)) (lazy-antecedent-rules kb % cpred))
                     (:antecedent rsx))))))

(defn- lazy-readers
  "The rules whose join proves an antecedent by one of the lazy-forward rules `lhs`
  (`proves-lazily?`), and on through each lazy-forward rule among them: the rules an
  arriving source of `lhs` owes a re-join.  Read over every context, as `fire-rules-for`
  reads.  Each record is read through `rsx-of`.  Nil, reading nothing, when `lhs` holds no
  lazy-forward rule's record."
  [kb lhs rsx-of]
  (when-let [handles (and (some #(some-> (rsx-of %) rules/lazy-sentex?) lhs)
                          (:handles (lazy-rules kb)))]
    (loop [todo (filterv handles lhs), seen #{}, out #{}]
      (if-let [h (first todo)]
        (if (contains? seen h)
          (recur (subvec todo 1) seen out)
          (let [f  (some-> (rsx-of h) :consequent nm/functor)
                rs (when (symbol? f)
                     (filterv #(proves-lazily? kb % f)
                              (reads/as-stored-rules-by-antecedent-global (:index kb) f)))]
            (recur (into (subvec todo 1) (filter handles) rs) (conj seen h) (into out rs))))
        (not-empty out)))))

;; a cycle: `join-stored` → `solve-lazy` → `planned-join` → `join-stored`
(declare solve-lazy)

;; ---- a transitive antecedent reads the closure, with the edges it crossed ----
;; An antecedent on a `(transitive P)` predicate is answered by `TransitivePredicateProver`
;; as well as by matching, and its predicate set is a taxonomy read, so it cannot be a
;; set on the prover.  The closure's answers are unioned with the matcher's, per reader
;; context, so a hop is crossed only where it is visible (docs/inference.md, "Seeding a
;; transitive closure").

(defn- walks-its-own-conclusion?
  "Does the rule being fired conclude on the walked predicate `pred` itself, or on a
  sub-predicate of it?  Such a rule is the closure written out, and the walk must not also
  run, or two chainers agreeing about every belief would record different antecedents for
  one conclusion.  A property of the rule, so independent of arrival order.  One direction:
  `pred` in `genls*(cpred)`, reflexive.  The `genls` read is unscoped.  See
  docs/inference.md."
  [kb pred cpred]
  (let [tx (reasoning/taxonomy kb)]
    (boolean (and cpred (symbol? cpred)
                  (contains? (tax/genls-global tx cpred) pred)))))

(defn- transitive-antecedent?
  "Is `ante` a binary literal whose own functor this KB declares `(transitive P)`, and
  therefore one the join can solve by walking the stored edges as well as by matching?
  `genl` and `genlCx` are excluded, and so is a rule that concludes on what it would walk
  (`walks-its-own-conclusion?`, `cpred` the consequent predicate or nil).  One map read on
  a KB that declares no transitive predicate.  The mark is read unscoped."
  [kb ante cpred]
  (and (sequential? ante) (= 3 (count ante))
       (let [f (nm/functor ante)]
         (and (symbol? f) (not (sx/variable? f))
              (not (contains? provers/transitive-predicates f))
              (contains? (tax/props (reasoning/taxonomy kb) :transitive) f)
              (not (walks-its-own-conclusion? kb f cpred))))))

(defn- transitive-source-preds
  "The predicates a walk over `pred` reads its hops from — `pred`'s own sub-predicates,
  plus every partner an `inverse` records a hop on.  `provers/hop-patterns`' step relation,
  named as a set so `provers/source-contexts` can say which contexts hold such an edge.

  Global rather than scoped, and over-approximating in the harmless direction: a context
  holding only a hop the reader cannot see is enumerated, walks nothing it can see, and
  answers nothing."
  [kb pred]
  (let [tx (reasoning/taxonomy kb)]
    (into (tax/specs-global tx pred) (tax/inverses-under tx pred))))

(defn- transitive-contexts
  "The contexts a walk over `pred` is worth asking at: those holding a hop
  (`transitive-source-preds`) or a `(transitive pred)` declaration, and those where two or
  more of them meet.  The declaration is a party because the walk reads it at the reader:
  hops in one context and the declaration in another compose only below both, and a
  context holding hops alone walks none."
  [kb pred]
  (provers/source-contexts kb (transitive-source-preds kb pred)
                           (tax/prop-supporters (reasoning/taxonomy kb) :transitive pred)))

;; ---- a genl / genlCx antecedent reads the cached closure ------------------------
;; `TransitivityProver` answers a `genl` or `genlCx` goal from the cached closure, so the
;; closure arm adds the closure's answers to the matcher's.  A `genl` pair two terms apart
;; is recorded as a closure link on `:matched`, a `[key nil [sub super]]` entry that
;; `subsumption-links` hands to placement.  A `genlCx` pair names the edges of one path
;; on `:handles`, the strongest by defeat class.  A reflexive pair rests on no edge.

(defn- closure-antecedent?
  "Is `ante` a positive binary literal on `genl` or `genlCx` — one the join answers from
  the cached closure as well as from the stored edges?

  A rule that concludes on the relation it reads is excluded, for the reason
  `walks-its-own-conclusion?` gives the transitive arm: its conclusions are edges of the
  closure it would read, so the path a firing names would depend on how far the rule had
  got.  Such a rule reads the stored edges, and its conclusions are stored edges too."
  [kb ante cpred]
  (and (sequential? ante) (= 3 (count ante))
       (contains? provers/transitive-predicates (nm/functor ante))
       (not (walks-its-own-conclusion? kb (nm/functor ante) cpred))))

(defn- solve-closure
  "Solve a `genl` / `genlCx` antecedent from the cached closure, per join state.  Bounded
  arms only: both ends bound is a membership test; one end bound reads that end's closure,
  the reflexive member included (as `TransitivityProver` does).  Both ends open, or an open
  end that is a pattern, contributes nothing.  The `genl` closure is read globally, as
  `subsumption-links` reads it; the `genlCx` closure from the lower context, dropping a pair
  whose path the witness context cannot see.  See docs/taxonomy.md."
  [kb ante states]
  (let [tx     (reasoning/taxonomy kb)
        rel    (nm/functor ante)
        genl?  (= 'genl rel)
        up     (if genl? #(tax/genls-global tx %) #(tax/context-up tx %))
        down   (if genl? #(tax/specs-global tx %) #(tax/context-down tx %))
        ak     (rules/antecedent-key ante)
        tms    (reasoning/tms kb)
        ground sx/ground-term?
        pairs  (fn [a b]
                 (cond
                   (and (ground a) (ground b)) (when (contains? (up a) b) [[a b {}]])
                   (and (ground a) (sx/variable? b)) (map (fn [y] [a y {b y}]) (up a))
                   (and (sx/variable? a) (ground b)) (map (fn [x] [x b {a x}]) (down b))))]
    (for [{:keys [bindings handles matched]} states
          :let [[_ a b] (res/substitute ante bindings)]
          [x y bnd] (pairs a b)
          :let [path (cond
                       (= x y) []
                       genl?   [[ak nil [x y]]]
                       :else   (tax/reach-support tx :genlCx x y x
                                                  #(jtms/defeat-class tms %)))]
          :when path]
      (cond
        (= x y) {:bindings (merge bindings bnd) :handles handles :matched matched}
        genl?   {:bindings (merge bindings bnd) :handles handles :matched (into matched path)}
        :else   {:bindings (merge bindings bnd) :handles (into handles (map first) path)
                 :matched  matched}))))

;; ---- a disjoint antecedent reads the separations ----------------------------
;; `DisjointnessProver` answers a `disjoint` goal from the taxonomy's separations: a
;; stated `disjoint` over a supertype of each side, a `partition` or `separating` declaration,
;; a `disjoint_metatype` and a `sibling_disjoint` parent.  The matcher reads only the
;; stated sentence, so the separation arm below unions the separations' answers with the
;; matcher's, as the closure arm does for `genl`.
;;
;; A separation answer names no stored tuple.  Each answer is one route
;; (`tax/separation-routes`): the declarations the route reads go on `:handles`, one
;; believed supporter per key, and the `genl` subsumptions it climbs go on `:matched` as
;; closure links, so placement lands the conclusion where a path is visible and names the
;; path's edges.  The join reads no `siblingDisjointException`: an exception exempts a
;; pair at the readers that see it, so `separation-exempted?` asks at the conclusion's
;; context.

(defn- key-supporters
  "The believed supporters of the flat-cache key `k`, as `[handle context]` in handle
  order, held for a reading pass (`tax/pass-held`)."
  [kb k]
  (tax/pass-held
   [::key-supporters k]
   #(let [tms  (reasoning/tms kb)
          recs (:records kb)]
      (into [] (comp (filter (fn [h] (jtms/in? tms h)))
                     (map (fn [h] [h (:context (p/get-sentex recs h))])))
            (sort (tax/visible-supporters (reasoning/taxonomy kb) k nil))))))

(defn- route-supporters
  "Each choice of one believed supporter per flat-cache key of `ks`, as a vector of
  `[handle context]`, in handle order key by key.  With `keep?`, only the choices whose
  every supporter `keep?` holds of with its key, `(keep? k [handle context])`, in the
  same order."
  ([kb ks] (route-supporters kb ks nil))
  ([kb ks keep?]
   (reduce (fn [acc k]
             (let [ws (cond->> (key-supporters kb k) keep? (filterv #(keep? k %)))]
               (for [xs acc, w ws] (conj xs w))))
           [[]] ks)))

(defn- separation-literal?
  "Is `ante` a positive binary literal on `disjoint`?"
  [ante]
  (and (sequential? ante) (= 3 (count ante)) (= 'disjoint (nm/functor ante))))

(defn- separation-antecedent?
  "Is `ante` a `disjoint` literal the join answers from the separations as well as from
  the stored sentences?  A rule concluding `disjoint`, or a sub-predicate of it, takes
  the matcher alone, for `closure-antecedent?`'s reason."
  [kb ante cpred]
  (and (separation-literal? ante)
       (not (walks-its-own-conclusion? kb 'disjoint cpred))))

(defn- separated-from
  "Every type a declaration separates from `t`, read globally and with no exception
  exempting a pair: the subtypes of each `tax/separating-partners` answer.  Global for
  `solve-separation`'s reason."
  [tx t]
  (distinct (mapcat #(tax/specs-global tx %)
                    (tax/separating-partners tx t nil (constantly false)))))

(defn- solve-separation
  "Solve a `disjoint` antecedent from the separations, per join state: one solution per
  route `tax/separation-routes` gives and per choice of believed supporters for the keys the
  route reads.  Both ends bound reads the routes between them; one end bound reads the routes
  to every type `separated-from` the bound end (the set `DisjointnessProver` answers); both
  ends open contributes nothing.  A bound end's `tax/separation-test` is read once per call.
  The separations are read globally, as `solve-closure` reads the closure, and the exception
  is asked at placement (`separation-exempted?`)."
  [kb ante states]
  (let [tx     (reasoning/taxonomy kb)
        ak     (rules/antecedent-key ante)
        ground sx/ground-term?
        sep    (memoize #(tax/separation-test tx % nil (constantly false)))
        routes (fn [a b]
                 (cond
                   (and (ground a) (ground b))
                   (when-let [t (sep a)]
                     (when (t b) (map #(vector % {}) (tax/separation-routes tx a b))))
                   (and (ground a) (sx/variable? b))
                   (for [y (separated-from tx a), r (tax/separation-routes tx a y)] [r {b y}])
                   (and (sx/variable? a) (ground b))
                   (for [x (separated-from tx b), r (tax/separation-routes tx x b)] [r {a x}])))]
    (for [{:keys [bindings handles matched]} states
          :let [[_ a b] (res/substitute ante bindings)]
          [{ks :keys links :links} bnd] (routes a b)
          sups (route-supporters kb ks)
          ;; a route over the stated sentence the literal names, with no edge climbed, is
          ;; the matcher's own hit, which the arrival filter already admits or declines
          :when (not (and (empty? links)
                          (every? #(= (res/substitute ante (merge bindings bnd))
                                      (:sentence (p/get-sentex (:records kb) (first %))))
                                  sups)))]
      {:bindings (merge bindings bnd)
       :handles  (into handles (map first) sups)
       :matched  (into matched (map #(vector ak nil %)) links)})))

(defn- separation-denial-antecedent?
  "Is `ante` a negated unary literal `(not (T a))` on a type `T` a separation reaches
  (`tax/separable?`), which the join answers from the separations as well as from the
  stored negations?"
  [kb ante]
  (and (rules/negative-literal? ante)
       (let [b (second ante)
             t (first b)]
         (and (= 2 (count b)) (not (sx/variable? t))
              (tax/separable? (reasoning/taxonomy kb) t)))))

(defn- solve-separation-denial
  "Solve a `separation-denial-antecedent?` per join state: one solution per believed
  membership `(S x)` of its argument stated in any context (`res/type-memberships`), per
  route separating `S` from `T` (`tax/separation-routes-held`), and per choice of believed
  supporters for its keys, a `[:member m y]` key taking only a `:monotonic` one.  The
  route's links go on `:matched` under `[:not T]`, so placement holds them at `:monotonic`
  (`negated-links`).  An open argument contributes nothing.  The exception is asked at
  placement (`separation-exempted?`)."
  [kb ante states]
  (let [tx    (reasoning/taxonomy kb)
        ak    (rules/antecedent-key ante)
        t     (first (second ante))
        cls   (delay (res/holding-class kb))
        keep? (fn [k [h]] (or (not= :member (first k)) (= :monotonic (@cls h))))]
    (for [{:keys [bindings handles matched]} states
          :let [x (second (second (res/substitute ante bindings)))]
          :when (sx/ground-term? x)
          m (res/type-memberships kb x '?ctx)
          :let [s (nm/functor (:sentence m))]
          :when (and (not= s t) (tax/pair-separated? tx s t))
          r    (tax/separation-routes-held tx s t)
          sups (route-supporters kb (:keys r) keep?)]
      {:bindings bindings
       :handles  (into (conj handles (:id m)) (map first) sups)
       :matched  (into matched (map #(vector ak nil %)) (:links r))})))

(defn- separation-exempted?
  "Does the reader `pctx` read some `disjoint` antecedent of `antes`, ground under
  bindings `b`, as no separation, while no believed sentence `pctx` sees states it?  A
  `siblingDisjointException` that `pctx` sees, or a `genl` edge that makes two marked
  types genl-related, spares a pair the join read separated, and the firing is then
  refused or blocked there.  A `separation-denial-antecedent?` is read the same way:
  `pctx` sees no believed negation of it and the level-6 question denies it nothing
  (`provers/exception-holds?`), which reads a separation and a closed extent alike."
  [kb antes b pctx]
  (let [tx  (reasoning/taxonomy kb)
        tms (reasoning/tms kb)]
    (boolean
     (some (fn [ante]
             (cond
               (separation-literal? ante)
               (let [[_ x y :as g] (res/substitute ante b)]
                 (and (sx/ground-term? x) (sx/ground-term? y)
                      (not (tax/disjoint? tx x y pctx))
                      (not-any? #(jtms/in? tms (first %)) (res/matches-visible kb g pctx))))

               (separation-denial-antecedent? kb ante)
               (let [g (res/substitute ante b)]
                 (and (sx/ground-term? (second (second g)))
                      (not-any? #(jtms/in? tms (first %)) (res/matches-visible kb g pctx))
                      (not (provers/exception-holds? kb [g] {} pctx))))))
           antes))))

(defn- mirrored-antecedent?
  "Is `ante` a literal the matcher answers through the symmetric mirror: a binary literal
  any of whose sub-predicates is declared `symmetric` (`res/raw-match`)?  Such a position
  takes no arrival filter, since the join (`*matcher*`) probes both argument orders where
  the trigger (`res/match1`) does not.  The declared symmetric predicates (a handful) are
  tested against the sub-predicate closure, which for a broad functor is the whole type
  hierarchy.  The mark is read unscoped."
  [kb ante]
  (and (sequential? ante) (= 3 (count ante))
       (let [f (nm/functor ante)]
         (and (symbol? f) (not (sx/variable? f))
              (let [tx    (reasoning/taxonomy kb)
                    specs (res/sub-predicates kb f nil)]
                (boolean (some #(contains? specs %) (tax/props tx :symmetric))))))))

(defn- permuting-antecedent?
  "Could the matcher answer `ante` from a stored fact read in an order other than the one
  it is stored in: a positive literal any of whose sub-predicates carries `symmetric` (at two
  arguments) or a commutativity group, or one holding a compound below it that
  `res/nested-probes` fans?  The presence check in front of `read-marks`.  Wider than
  `mirrored-antecedent?`, since the trigger fans a commuting antecedent's arrangements
  itself (`trigger-bindings`).  The marks are read unscoped."
  [kb ante]
  (and (sequential? ante) (next ante)
       (let [f (nm/functor ante)]
         (and (symbol? f) (not (sx/variable? f)) (not= sx/not-functor f)
              (let [tx   (reasoning/taxonomy kb)
                    syms (tax/props tx :symmetric)]
                (and (or (seq syms) (tax/commuting-declared? tx))
                     (let [specs (res/sub-predicates kb f nil)]
                       (boolean (or (and (= 3 (count ante)) (some #(contains? specs %) syms))
                                    (tax/commuting-predicates-among tx specs)
                                    (next (res/nested-probes kb ante)))))))))))

(defn- probed-read-marks
  "The alternative sets of mark handles a read of the stored `sentence` as the literal `g`
  through a mention probe (`res/mention-probes`) rests on: per argument holding a compound
  in another order than `g`'s, the marks licensing that order
  (`inherit/permuted-read-supports` over the compound).  Nil when no argument differs."
  [kb g sentence]
  (let [pairs (filter (fn [[t s]] (and (seq? t) (seq? s) (not= t s))) (map vector (rest g) (rest sentence)))]
    (when (seq pairs)
      (reduce (fn [alts [t s]]
                (for [a alts, k (or (inherit/permuted-read-supports kb s (vec (rest t)) '?ctx) [[]])]
                  (into a k)))
              [[]] pairs))))

(defn- read-marks
  "The alternative sets of mark handles a match of `pattern` under `b` rests on, when the
  stored fact at `h` was read in another argument order (`inherit/permuted-read-supports`,
  `probed-read-marks`), else `[[]]` — one firing naming nothing more, as every unpermuted
  match is."
  [kb pattern b h stored]
  (let [sxr (if (:sentence stored) stored (p/get-sentex (:records kb) h))
        sen (:sentence sxr)
        g   (res/substitute pattern b)]
    (or (when (sequential? sen)
          (or (inherit/permuted-read-supports kb sen (vec (rest g)) '?ctx)
              (when (seq (res/mention-probes kb g)) (probed-read-marks kb g sen))))
        [[]])))

(defn- symmetric-mirror
  "The mirror of `fact` when the KB reads it as one (a binary literal whose own predicate
  is declared `symmetric`, and whose arguments differ), else nil.  Asked of the fact, once
  per datum.  The mark is read unscoped."
  [kb fact]
  (when (and (sequential? fact) (= 3 (count fact)))
    (let [f (nm/functor fact)]
      (when (and (symbol? f) (not (sx/variable? f))
                 (contains? (tax/props (reasoning/taxonomy kb) :symmetric) f))
        (let [m (sx/mirror-literal fact)]
          (when-not (= m fact) m))))))

(defn- commuting-components-of
  "The commuting components `fact`'s own predicate licences at its own arity, or nil.

  Asked of the **fact** for `symmetric-mirror`'s reason: it is the fact's declaration that
  makes its permutations true, and a super-predicate carrying the mark says nothing about
  the sub the fact is stated at.  Read once per datum, since every antecedent position
  asks the same fact.

  The groups are read unscoped, for `mirrored-antecedent?`'s reason."
  [kb fact]
  (when (and (sequential? fact) (next fact))
    (let [f (nm/functor fact)]
      (when (and (symbol? f) (not (sx/variable? f)))
        (sx/commuting-components (tax/commuting-groups (reasoning/taxonomy kb) f)
                                 (dec (count fact)))))))

(defn- trigger-bindings
  "The binding maps a datum makes at one antecedent position: what `fact` unifies to,
  what its symmetric `mirror` unifies to, and what each arrangement of the antecedent under
  `comps` unifies to, each kept when it binds differently and deduplicated.  It rearranges
  the antecedent (`sentex/arrangements-over`), each compound below it holding a variable
  (`res/nested-probes`) and each compound at a mention some reader does not read
  (`res/mention-probes`), so a permuting antecedent at the trigger position reads as it
  does at a join position."
  [kb ante fact mirror comps]
  (let [one (fn [a]
              (concat [(res/match1 kb a fact) (when mirror (res/match1 kb a mirror))]
                      (when comps
                        (keep #(res/match1 kb % fact) (rest (sx/arrangements-over a comps))))))]
    (not-empty (into [] (comp (mapcat one) (remove nil?) (distinct))
                     (concat (res/nested-probes kb ante) (res/mention-probes kb ante))))))

(def ^:dynamic *evaluatable-preds*
  "Per-run cache of the KB's `add-evaluatable` predicate functors
  (`provers/evaluatable-preds`) — the ones forward chaining computes through the prover
  registry instead of looking up as stored facts, exactly as it does the built-in
  `sentex/deferred-predicates`.  Bound once per run by `chain`, since the registry is
  fixed for the run and rebuilding the set per antecedent would allocate on the hot join
  path.  Nil outside a run — the `solve-rule` `why-not` reaches through, say — where
  `deferred-antecedent?` reads the registry directly.  Empty for the common KB with no
  registered evaluatables."
  nil)

(defn- evaluatable-antecedent-preds
  "This KB's registered evaluatable functors, from the per-run cache when a chaining run
  has bound it, else read straight off the registry (`provers/evaluatable-preds`)."
  [kb]
  (or *evaluatable-preds* (provers/evaluatable-preds kb)))

(defn- deferred-antecedent?
  "Is `ante` a computed antecedent for `kb`: a built-in evaluable
  (`sentex/deferred-predicates`) or a predicate registered with `add-evaluatable`?  Forward
  chaining discharges these through the prover registry (`solve-deferred`).  A registered
  evaluatable is placed by `planned-join` with `provers/evaluatable-est-override`.  The
  registered arm runs only on a non-empty predicate set."
  [kb ante]
  (or (sx/deferred-literal? ante)
      (let [preds (evaluatable-antecedent-preds kb)]
        (and (seq preds)
             (sequential? ante) (seq ante)
             (contains? preds (first ante))))))

(defn- fanning-functor?
  "Does `g`'s functor have a fan for the argument lead to collapse — a sub-predicate
  closure wider than the functor itself, or a **variable** functor, which names no
  predicate and so puts every argument behind it at level 0 of the trie?

  The closure is reflexive, so `> 1` is \"something other than the functor is in it\".
  Read at the wildcard vantage, which is the one `join-matches` matches at: the global
  closure, memoized on the taxonomy generation (`tax/specs`), so this is a cached set
  and a `count` rather than a walk."
  [kb g]
  (let [f (first g)]
    (or (sx/variable? f)
        (> (count (res/sub-predicates kb f '?ctx)) 1)
        (boolean (seq (res/swapped-sub-predicates kb f '?ctx))))))

(defn- join-matches
  "The stored facts satisfying the substituted antecedent `g` at the wildcard context:
  `[handle bindings …]` pairs, the set `res/match-pattern` returns.  `*matcher*` is the
  reference.  For a literal with a bound indexable argument and a functor with
  sub-predicates (`fanning-functor?`), `res/matches-hierarchical` leads from the argument's
  postings (`res/*lead-side*`); a functor with no sub-predicates keeps the trie
  (`join_lead_cost_test`).  The lead is taken only when the reference matcher is bound and
  `res/*hierarchical-retrieval*` is not false (`matches_hierarchical_test`).  Each
  `res/mention-probes` spelling of `g` is matched too (`mention-unread?`)."
  [kb g]
  (let [own (if (and res/*hierarchical-retrieval*
                     (identical? *matcher* res/match-pattern)
                     (res/lead-literal? g)
                     (fanning-functor? kb g))
              (res/matches-hierarchical kb g '?ctx)
              (*matcher* kb g '?ctx))
        ps  (res/mention-probes kb g)]
    (if (empty? ps)
      own
      (nm/distinct-by (fn [[h b]] [h b]) (concat own (mapcat #(*matcher* kb % '?ctx) ps))))))

(defn- join-stored-shape
  "The matcher's facts satisfying `ante` over `states0`, unioned with the answers of the
  arm that computes the literal's shape, if any."
  [kb ante states0 admit cpred stop]
  (let [states #(cut stop states0)
        ak    (rules/antecedent-key ante)
        calc  (qualitative-antecedent kb ante)
        keep? (when (and admit (nil? calc) (not (mirrored-antecedent? kb ante))) admit)
        perm? (or (permuting-antecedent? kb ante) (boolean (seq (res/mention-probes kb ante))))
        hits  (fn [{:keys [bindings handles matched]}]
                (let [g (res/substitute ante bindings)]
                  (for [[h b2 stored] (join-matches kb g)
                        :when (or (nil? keep?) (keep? h))
                        ;; a fact read in another argument order holds the
                        ;; firing only while a mark licensing that order does
                        ms (if perm? (read-marks kb g b2 h stored) [[]])]
                    {:bindings (merge bindings b2) :handles (into (conj handles h) ms)
                     :matched  (conj matched [ak h])})))
        hit   (mapcat hits (states))]
    (cond
      calc (distinct (concat hit (solve-qualitative kb calc ante (states))))
      (computed-antecedent? kb ante)
      (distinct (concat hit (solve-computed kb ante (states))))
      (closure-antecedent? kb ante cpred)
      (let [per (mapv (fn [st]
                        (let [cl  (solve-closure kb ante [st])
                              ans (into #{} (map #(dissoc (:bindings %) '?ctx)) cl)]
                          ;; a stored edge the closure answers too is matched as the
                          ;; closure's pair, so the firing is one justification in
                          ;; every arrival order
                          [(remove #(contains? ans (dissoc (:bindings %) '?ctx)) (hits st)) cl]))
                      (states))]
        (distinct (concat (mapcat first per) (mapcat second per))))
      (separation-antecedent? kb ante cpred)
      (distinct (concat hit (solve-separation kb ante (states))))
      (separation-denial-antecedent? kb ante)
      (distinct (concat hit (solve-separation-denial kb ante (states))))
      ;; a preserved transitive predicate joins on both: the walk crosses `inverse`
      ;; hops, the preserving join the reaches its declarations compose with it
      (transitive-antecedent? kb ante cpred)
      (distinct (concat hit (solve-computed kb ante (states)
                                            (transitive-contexts kb (nm/functor ante)))
                        (when (preserving-antecedent? kb ante '?ctx)
                          (solve-preserving kb ante (states) cpred))))
      (preserving-antecedent? kb ante '?ctx)
      (distinct (concat hit (solve-preserving kb ante (states) cpred)))
      :else hit)))

(defn- join-stored
  "`join-antecedent` for an antecedent the store answers: the matcher's facts, unioned
  with the answers of the arm that computes the literal's shape (qualitative, computed,
  closure, separation, transitive, preserving; `join-stored-shape`), if any, and with a
  lazy-forward rule's (`solve-lazy`).

  Each pass over `states` is cut by `stop` afresh (`join-antecedent`): the matcher's pass
  realizes the rows the computing arm then reads again, so a cut taken once would be
  spent before the arm's asks began."
  [kb ante states0 admit cpred stop]
  (let [lazy   (lazy-antecedent-rules kb ante cpred)
        joined (join-stored-shape kb ante states0 admit cpred stop)]
    (if lazy
      (distinct (concat joined (solve-lazy kb ante (cut stop states0) lazy stop)))
      joined)))

(defn- join-antecedent
  "Extend the partial join `states` ({:bindings :handles :matched}) by one antecedent.
  `admit` is the arrival filter on the handles this antecedent yields (`(fn [handle] ->
  boolean)` from `complete-antecedents`, or nil; `*agenda-arrivals*`).  Six positions
  decline it, because the join reaches a satisfier no trigger can: qualitative, computed,
  inherited, closure (`solve-closure`), separation (`solve-separation`) and mirrored
  (`mirrored-antecedent?`) antecedents.  A computed literal contributes the handles its
  answer was read from and no more (none for arithmetic comparisons, whose placeholder would
  be a support `retract!` cannot take away).  `:matched` pairs each ordinarily matched fact
  with the antecedent key it satisfied (`rules/antecedent-key`), for `subsumption-links`.
  `cpred` is the rule's consequent predicate, read by `transitive-antecedent?`.  `stop` is
  the bound `planned-join` cuts by (`cut`), or nil."
  [kb ante states admit cpred stop]
  (cond
    ;; An `(unknown S)` antecedent is negation as failure, checked at derive time in the
    ;; conclusion's placement context, as `exceptWhen` is.  It binds nothing, so the join
    ;; passes through; a condition that holds places a guard defeat (`place-guard-defeats!`).
    (sx/unknown? ante) states

    ;; An aggregate is evaluated per placement in `place-conseq` (docs/aggregate.md), and
    ;; `planned-join` withholds it; this arm passes it through for a direct caller.
    (sx/aggregate? ante) states

    ;; a value kind of a constant or a compound reads what is stored, as a literal
    ;; on any other predicate does
    (deferred-antecedent? kb ante)
    (mapcat (fn [{:keys [bindings handles matched] :as st}]
              (if (provers/term-value-kind-goal? (res/substitute ante bindings))
                (join-stored kb ante [st] admit cpred stop)
                (map (fn [[b sup]] {:bindings b :handles (into handles sup) :matched matched})
                     (solve-deferred kb ante bindings))))
            (cut stop states))

    :else (join-stored kb ante states admit cpred stop)))

(defn- open-ends
  "The two end variables of `ante` when it is a closure antecedent
  (`closure-antecedent?`) or a separation antecedent (`separation-antecedent?`) with both
  ends open, else nil.  `solve-closure` and `solve-separation` answer the pairs no
  sentence states only once an end is bound, so `plan/order` holds the literal back until
  a generator or the rule's recursive literal binds one (`:end-vars`).  Canonical order
  stores `(genl ?a ?b)` ahead of `(pairOf ?a ?b)`, so without this an unranked join reads
  only the edges."
  [kb ante cpred]
  (when (and (sequential? ante) (= 3 (count ante)))
    (let [[_ a b] ante]
      (when (and (sx/variable? a) (sx/variable? b)
                 (or (closure-antecedent? kb ante cpred) (separation-antecedent? kb ante cpred)))
        #{a b}))))

(defn- join-order
  "`antecedents` ordered by estimated fan-out under the bindings in hand (`b0`), the order
  `planned-join` joins them in: a pure cost decision (`plan/order`), as
  `res/planned-antecedents` makes for backward chaining.  Deferred and `unknown` literals
  never outrun their binders, the recursive literal stays put (`consequent-pred`), and a
  registered evaluatable is placed by cost (`:est-override`).  A closure or separation
  antecedent with both ends open waits for a binder (`open-ends`).  Post-join literals
  (`rules/post-join-literals`), closed-extent negative literals (docs/naf.md) and `different`
  literals are withheld (`refusal-reason`).  A held `disjoint` literal `lead` runs first."
  ([kb antecedents b0 consequent-pred] (join-order kb antecedents b0 consequent-pred nil))
  ([kb antecedents b0 consequent-pred lead]
   (let [subbed (mapv #(res/substitute % b0) antecedents)
         ;; a `disjoint` literal, or a negated one a separation denies, whose variables the
         ;; other literals all bind is joined after them: its arm answers bound ends, and a
         ;; `disjoint` one never enumerates the types separated from one end
         ce       (set (closed-extent-antecedents kb subbed))
         sep?     #(or (separation-literal? %)
                       (and (separation-denial-antecedent? kb %) (not (ce %))))
         bound-by (into #{} (comp (remove sep?) (mapcat sx/form-variables)) subbed)
         held   (filterv #(and (sep? %) (every? bound-by (sx/form-variables %))) subbed)
         subbed (if (seq held) (filterv (complement (set held)) subbed) subbed)
         held   (if lead (filterv #(not= lead %) held) held)
         ;; ...and a closed-extent negative literal, which is a test on what the conclusion's
         ;; context believes; it is decided in `derive-conclusion`, where `unknown` is.
         post   (-> (set (rules/post-join-literals subbed))
                    (into ce)
                    ;; ...and a `different` literal, a test on the partition the
                    ;; conclusion's context sees (`different-blocks?`)
                    (into (filter #(= 'different (nm/functor %))) subbed))
         ;; A registered evaluatable is placed after its binders by cost; a literal a
         ;; `SupportingProver` answers is costed by that prover, and a `disjoint` literal by
         ;; `DisjointnessProver` (`solve-separation`).  Every other antecedent is ranked by the
         ;; index model.
         ev     (provers/evaluatable-est-override kb (evaluatable-antecedent-preds kb))
         sp     (provers/support-est-override kb)
         dj     (provers/separation-est-override kb)
         est    (if ev
                  (fn [g b] (or (ev g b) (sp g b) (dj g b)))
                  (fn [g b] (or (sp g b) (dj g b))))]
     (into [] (remove post)
           (concat (when lead [lead])
                   (plan/order kb subbed '?ctx {:consequent-pred consequent-pred :est-override est
                                                :end-vars #(open-ends kb % consequent-pred)
                                                :bound (if lead (set (sx/form-variables lead)) #{})})
                   held)))))

(defn- separation-lead
  "The held `disjoint` literal of `order` that binds an end of a closure literal `order`
  reaches with both ends open, or nil.  That closure literal reads the stored edges alone,
  so a pair a stored `disjoint` sentence names and no edge states is read only by a join
  this literal leads (`planned-join`)."
  [kb order cpred]
  (when (some separation-literal? order)
    (loop [[l & more] order, bound #{}, open #{}]
      (when l
        (if (and (separation-antecedent? kb l cpred)
                 (every? bound (sx/form-variables l))
                 (some open (sx/form-variables l)))
          l
          (let [ends (when (closure-antecedent? kb l cpred) (open-ends kb l cpred))]
            (recur more (into bound (sx/form-variables l))
                   (if (and ends (not-any? bound ends)) (into open ends) open))))))))

(defn- planned-join
  "Join `antecedents` left to right from `seed`, in `join-order` under `b0`.  `admit` is
  the arrival filter (`join-antecedent`), per handle.  A row with no handle is dropped when
  the rule has an antecedent `solve-computed` answers.  `stop` is the bound of the run
  (`*stop*`), or nil for a join that tests a condition (`cut`).  `delta`, a set of source
  datum handles or nil, keeps past the last computed or lazy-forward antecedent only the
  rows holding one (`run-owed-rejoin`).  A `separation-lead` joins a second time from that
  literal, and a first-join row matching its stored sentence yields to the second join's."
  ([kb antecedents b0 consequent-pred seed admit stop]
   (planned-join kb antecedents b0 consequent-pred seed admit stop nil))
  ([kb antecedents b0 consequent-pred seed admit stop delta]
   (let [computed? (delay (some #(or (computed-antecedent? kb %)
                                     (transitive-antecedent? kb % consequent-pred))
                                antecedents))
         step      (fn [states ante]
                     (cut stop (join-antecedent kb ante states admit consequent-pred stop)))
         run       (fn [order]
                     (if-let [last-c (when delta
                                       (last (keep-indexed #(when (or (computed-antecedent? kb %2)
                                                                      (lazy-antecedent-rules kb %2 consequent-pred))
                                                              %1)
                                                           order)))]
                       (let [[pre post] (split-at last-c order)
                             states     (doall (reduce step (cut stop seed) pre))
                             rows       (binding [*lazy-delta* delta]
                                          (doall (step states (first post))))]
                         (reduce step (filter #(some delta (:handles %)) rows) (rest post)))
                       (reduce step (cut stop seed) order)))
         order     (join-order kb antecedents b0 consequent-pred)
         rows      (if-let [lead (separation-lead kb order consequent-pred)]
                     (let [led     (run (join-order kb antecedents b0 consequent-pred lead))
                           pair    #(dissoc (:bindings %) '?ctx)
                           led-at  (into #{} (map pair) led)
                           k       (rules/antecedent-key lead)
                           stated? (fn [row] (some (fn [[mk h]] (and (= k mk) (some? h))) (:matched row)))]
                       (concat led (remove #(and (stated? %) (led-at (pair %))) (run order))))
                     (run order))]
     (remove #(and (empty? (:handles %)) @computed?) rows))))

(defn- matched-only-antecedent?
  "Does the matcher alone answer `ante` in a join of a rule concluding on `cpred`, from
  facts read in their stored spelling: a positive literal on a constant functor that no
  arm of `join-stored-shape` computes, no lazy-forward rule proves, and no mark permutes
  (`permuting-antecedent?`, `mirrored-antecedent?`)?"
  [kb ante cpred]
  (let [f (when (sequential? ante) (first ante))]
    (and (symbol? f) (not (sx/variable? f)) (not= sx/not-functor f) (not= 'different f)
         (not (sx/unknown? ante)) (not (sx/aggregate? ante)) (not (separation-literal? ante))
         (= ante (res/probe-spelling kb ante))
         (not (deferred-antecedent? kb ante))
         (nil? (qualitative-antecedent kb ante))
         (not (computed-antecedent? kb ante))
         (not (closure-antecedent? kb ante cpred))
         (not (transitive-antecedent? kb ante cpred))
         (not (preserving-antecedent? kb ante '?ctx))
         (not (permuting-antecedent? kb ante))
         (not (mirrored-antecedent? kb ante))
         (nil? (lazy-antecedent-rules kb ante cpred)))))

(defn- delta-lazy-rows
  "The rows of the join of the lazy-forward rule `rh`'s renamed antecedents `antes` under
  `b0` that rest on a handle of `delta`, joined from those datums: each believed one
  matched (`res/match1`) at each antecedent it unifies with, the others joined from there.
  Nil when an antecedent is not `matched-only-antecedent?` or a datum reads in another
  argument order, and `solve-lazy` then joins in full."
  [kb antes b0 cpred rh delta stop]
  (let [subbed (mapv #(res/substitute % b0) antes)
        tms    (reasoning/tms kb)
        blind? (res/belief-blind?)]
    (when (every? #(matched-only-antecedent? kb % cpred) subbed)
      (let [facts (into [] (keep (fn [d]
                                   (when (or blind? (jtms/in? tms d))
                                     (when-let [f (:sentence (p/get-sentex (:records kb) d))]
                                       [d f]))))
                        (sort delta))]
        (when-not (some (fn [[_ f]] (or (symmetric-mirror kb f) (commuting-components-of kb f))) facts)
          (into [] (distinct)
                (for [[d f] facts
                      i     (range (count subbed))
                      :let  [a (nth subbed i)
                             b (res/match1 kb a f)]
                      :when b
                      row   (planned-join kb (into (subvec subbed 0 i) (subvec subbed (inc i)))
                                          (merge b0 b) cpred
                                          [{:bindings (merge b0 b) :handles [rh d]
                                            :matched  [[(rules/antecedent-key a) d]]}]
                                          nil stop)]
                  row)))))))

(defn- solve-lazy
  "Prove `ante` per join state by the lazy-forward rules `rs` (`lazy-antecedent-rules`):
  each rule's variables renamed apart, its antecedents joined (`planned-join`) under the
  bindings that unify its consequent with the substituted literal, and each row's
  conclusion unified back.  A row adds the rule's handle and the join's handles and
  `:matched`, so placement reads the edges a subsumption match climbed.  Under
  `*lazy-delta*`, a state resting on no datum of it is proved from those datums
  (`delta-lazy-rows`)."
  [kb ante states rs stop]
  (let [depth (inc (count *lazy-solving*))
        delta *lazy-delta*]
    (distinct
     (for [{:keys [bindings handles matched]} states
           :let [g    (res/substitute ante bindings)
                 owed (when (and delta (not-any? delta handles)) delta)]
           r rs
           :let [m  (into {} (map (fn [v] [v (symbol (str "?lz" depth (subs (name v) 1)))]))
                          (sx/form-variables (cons (:consequent r) (:antecedent r))))
                 c  (sx/rename-vars (:consequent r) m)
                 lv (set (vals m))
                 b0 (some->> (res/unify c g)
                             (into {} (filter (fn [[k v]] (and (lv k) (sx/ground-term? v))))))]
           :when b0
           row (binding [*lazy-solving* (conj *lazy-solving* (:id r)), *lazy-delta* nil]
                 (let [antes (mapv #(sx/rename-vars % m) (:antecedent r))]
                   (or (when owed (delta-lazy-rows kb antes b0 (nm/functor c) (:id r) owed stop))
                       (doall (planned-join kb antes b0 (nm/functor c)
                                            [{:bindings b0 :handles [(:id r)] :matched []}]
                                            nil stop)))))
           :let [b (res/unify g (res/substitute c (:bindings row)))]
           :when b]
       {:bindings (merge bindings b) :handles (into handles (:handles row))
        :matched  (into matched (:matched row))}))))

(defn- closure-bound?
  "Does `planned-join` reach closure antecedent `ante`, one of `antecedents`, with an end
  bound, so that `solve-closure` answers it?  An end is bound when it is ground as written
  or a literal joined before `ante` binds every variable in it."
  [kb antecedents ante cpred]
  (let [open (remove #(empty? (sx/form-variables %)) (rest ante))]
    (or (< (count open) 2)
        (let [bound (into #{} (comp (take-while #(not= ante %)) (mapcat sx/form-variables))
                          (join-order kb antecedents {} cpred))]
          (boolean (some #(every? bound (sx/form-variables %)) open))))))

(defn- closure-trigger-seed
  "The states a trigger at closure antecedent `ante` seeds the rest of the join with: the
  closure's answer for the pair the trigger bindings `b0` name, which is how the full join
  records that pair when it reaches `ante` with an end bound (`join-antecedent`).  Nil
  when `ante` is no closure antecedent, the full join reaches it with both ends open, or
  the closure does not hold the pair; the trigger then seeds with its handle."
  [kb antecedents ante b0 cpred]
  (when (and (closure-antecedent? kb ante cpred) (closure-bound? kb antecedents ante cpred))
    (not-empty (vec (solve-closure kb ante [{:bindings b0 :handles [] :matched []}])))))

(defn- arrival-admit
  "The filter `complete-antecedents` puts on the handles the join yields, or nil when
  there is nothing to suppress: no ledger bound, a trigger the run never enqueued, or a
  trigger that is not believed (an OUT datum fires its rules through `res/match1` and no
  other trigger's join finds it).  Admits a candidate whose arrival is at or before the
  trigger's, as semi-naive evaluation on an agenda; a handle with no arrival is admitted.
  `<=` admits a self-join twice and the dedup rejects the second.  See docs/inference.md,
  \"What a run pays per witness\"."
  [kb trigger-handle]
  (when-let [^java.util.Map arrivals *agenda-arrivals*]
    (when-let [at (.get arrivals trigger-handle)]
      (when (jtms/in? (reasoning/tms kb) trigger-handle)
        (let [at (long at)]
          (fn [h] (let [a (.get arrivals h)] (or (nil? a) (<= (long a) at)))))))))

(defn- rule-arrival-admit
  "`arrival-admit` for a rule datum's full join (`process-datum`): admit a fact that
  reached this run's agenda no later than the rule did, or never reached it.  The
  participant that arrived last enumerates the firing (`fire-rules-for`, `later-rule?`).
  Nil outside a chaining run or for a rule the run never enqueued."
  [rule-handle]
  (when-let [^java.util.Map arrivals *agenda-arrivals*]
    (when-let [at (.get arrivals rule-handle)]
      (let [at (long at)]
        (fn [h] (let [a (.get arrivals h)] (or (nil? a) (<= (long a) at))))))))

(defn- complete-antecedents
  "Enumerate {:bindings :handles} completions of a rule fired at position `trigger-idx` by
  `trigger-handle`, joining the other antecedents from facts in any context, in cost order
  (`planned-join`), over facts that reached this run's agenda no later than the trigger
  (`arrival-admit`).  The join passes `'?ctx` because admissibility is placement's question
  (`place-conseq`, recorded as `:no-placement`).  A deferred literal at the trigger position
  is computed and the trigger handle dropped, so a computed literal draws no support from a
  stored twin.  `marks` are the alternative sets of mark handles the trigger's match rests on
  (`read-marks`), `[[]]` for a fact unified as stored; each seeds its own join.  A trigger
  at a closure antecedent seeds with the closure's answer (`closure-trigger-seed`)."
  [kb antecedents trigger-idx trigger-handle b0 marks consequent-pred]
  (let [trigger-ante (nth antecedents trigger-idx)
        handle-only? (not (deferred-antecedent? kb trigger-ante))
        to-join      (if handle-only?
                       (vec (keep-indexed (fn [j a] (when (not= j trigger-idx) a)) antecedents))
                       (vec antecedents))
        seed         (or (when handle-only?
                           (closure-trigger-seed kb antecedents trigger-ante b0 consequent-pred))
                         (vec (for [ms (if handle-only? marks [[]])]
                                {:bindings b0
                                 :handles  (if handle-only? (into [trigger-handle] ms) [])
                                 ;; the trigger is a match like any other, and it is the
                                 ;; one most likely to have subsumed: `fire-rules-for`
                                 ;; reaches a rule through the arriving fact's *supertypes*
                                 :matched  (if handle-only?
                                             [[(rules/antecedent-key trigger-ante) trigger-handle]]
                                             [])})))]
    ;; a *deferred* trigger draws no handle at all, so there is no arrival to order the
    ;; rest of the join against and nothing is suppressed
    (planned-join kb to-join b0 consequent-pred seed
                  (when handle-only? (arrival-admit kb trigger-handle)) *stop*)))

(defn solve-rule
  "Full join of a rule's antecedents against current facts (used when a rule is
  added), in cost order.  The seeded arity starts from `b0` instead of the empty
  binding map, which is how `why-not` reconstructs a firing backwards from its
  conclusion; `consequent-pred` (the rule's consequent functor, nil if unknown) lets
  the planner keep the recursive literal in place."
  ([kb antecedents] (solve-rule kb antecedents {} nil))
  ([kb antecedents b0] (solve-rule kb antecedents b0 nil))
  ([kb antecedents b0 consequent-pred]
   ;; no trigger, so no arrival to order against: a full join suppresses nothing; and a
   ;; test (a guard's condition, `why-not`), so the run's bound does not cut it
   (planned-join kb (vec antecedents) b0 consequent-pred
                 [{:bindings b0 :handles [] :matched []}] nil nil)))

(defn- free-consequent-vars
  "The variables remaining in a rule's substituted conclusion `form` — the head
  existential variables the antecedent bindings did not cover.  Empty for an ordinary
  range-restricted rule, so this is the cheap test for whether skolemization applies.

  A direct walk rather than `tree-seq` + `filter` + `distinct`, because it runs **per
  firing** and its answer is almost always nil: those three compose into a lazy seq
  apiece over a form that is usually `(pred a b)`, where the walk they wrap is three
  `cond` arms.  Nothing is allocated until a variable is actually found."
  [form]
  (letfn [(walk [acc x]
            (cond
              (sx/variable? x) (if (some #(= x %) acc) acc (conj acc x))
              (sequential? x)  (reduce walk acc x)
              :else            acc))]
    (seq (walk [] form))))

(defn- directed-generated-rule
  "The rule a generator generated, `sentence`, with the direction it is stored under.

  A generated rule defaults to forward (forward + backward): a generator exists to
  materialize, and its generated rule is the generator's product, so it forward-chains
  unless the author wrote a direction wrapper on it (which rides in the sentence and
  survives substitution).  Without this default a bare generated rule would take the
  ordinary backward default and never fire — a generator that generates nothing live."
  [sentence]
  (if (first (sx/peel-rule-wrapper sentence))
    sentence
    (rules/wrap-direction sentence :forward)))

(defn- generated-rule-violation
  "The first check violation of the rules a generated `sentence` is stored as in `pctx`,
  or nil — `mint-rule`'s check list, over every rule the polycanonicalization stores."
  [kb sentence pctx]
  (some #(checks/rule-violation kb % pctx)
        (rules/expand-rule (directed-generated-rule sentence))))

;; `place-conseq` declines to place a firing a closed-extent negative antecedent or a
;; separation spares, which leaves no justification and nothing in `jtms/blocked`, so the
;; refusal is recorded as `[rule-handle, bindings]` for a re-ask (docs/exceptions.md, "A
;; refused firing is remembered as bindings").
;;   closed extent     recorded as `:naf`, re-askable from the bindings alone
;;   spared pair       recorded as `:separation`, re-asked when a `siblingDisjointException`
;;                     or `genl` edge arrives or leaves
;;   post-join failure not recorded (`settle/rejoin-on-arrival-rules`)
;;   `except`-hidden   not recorded; no trigger queues the rule on one
;; A firing the settle blocks after its placement is recorded the same way
;; (`record-swept-firing!`).  A conclusion an argument declaration convicts is stored and
;; held OUT (`checks/hold-argument-conviction!`).  The record is a work list and never an
;; answer: each entry is re-decided when read (`refusal-state`), keyed on content.

(def max-refusals-per-rule
  "How many refused firings one rule's record keeps before it stops keeping them
  individually.  Past it the rule's record collapses to `:overflow` and a queued overflowed
  rule forces a productive settle pass and a re-join over its extent (docs/exceptions.md)."
  4096)

(defn- record-refusal!
  "Remember that a firing of `rule` was refused: the conclusion it would have placed,
  where, what it rests on, and the bindings the block condition was asked under, less the
  join's `?ctx`.  `antes` is every antecedent, the rule included, in content order, and
  `:handles` every one but the rule, so a firing refused by either join or swept is one
  entry.  `:max-depth` is the refusing run's derivation-depth bound, which
  `release-refusal!` reads in a settle with no run config; two bounds keep the wider, nil
  (none) over a number.  The term-nesting bound is not kept.  `extra` (a subsumed firing's
  `:subsumptions`) joins the entry's identity."
  [kb rule conseq pctx antes bindings max-depth extra]
  (let [rh    (:rule-handle rule)
        entry (merge {:conseq conseq :pctx pctx :antes antes :handles (into [] (remove #{rh}) antes)
                      :bindings (dissoc bindings '?ctx) :max-depth max-depth}
                     extra)
        id    (dissoc entry :max-depth)
        h     (hash conseq)
        same  (fn [cur] (some #(when (and (== h (hash (:conseq %))) (= id (dissoc % :max-depth))) %) cur))
        wider #(and (some? %2) (or (nil? %1) (> (long %1) (long %2))))]
    (swap! (reasoning/refused kb)
           (fn [m]
             (let [cur (get m rh)]
               (cond
                 (= :overflow cur)
                 m
                 (contains? cur entry)
                 m
                 :else
                 (if-let [old (same cur)]
                   (cond-> m (wider max-depth (:max-depth old)) (assoc rh (conj (disj cur old) entry)))
                   (if (and cur (>= (count cur) max-refusals-per-rule))
                     (assoc m rh :overflow)
                     (assoc m rh (conj (or cur #{}) entry))))))))))

(defn record-swept-firing!
  "Record the rule firing whose justification record is `j` as a refusal, when the settle
  blocks it after its placement and the sweep deletes it, so the trigger that lifts the block
  releases it from its bindings (`release-refusal!`).  `:handles` is every antecedent but the
  rule.  Records nothing for a firing whose rule does not forward-chain (`refusal-state`
  reads that entry as `:dead`), whose antecedent an `except` hides, or whose post-join
  literal no longer answers.  Runs before the sweep deletes the conclusion's record."
  [kb j]
  (let [rh  (:informant j)
        rsx (when (integer? rh) (p/get-sentex (:records kb) rh))]
    (when (and rsx (rules/forward-sentex? rsx))
      (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
        (let [antes (vec (:antecedents j))
              pctx  (:context csx)]
          (when-not (or (antecedent-hidden? kb antes pctx)
                        (post-join-withdrawn? kb rsx
                                              (delay (settled-bindings kb (:bindings j) pctx))
                                              pctx))
            (record-refusal! kb {:rule-handle rh} (:sentence csx) pctx (kb/antecedent-order kb (conj antes rh))
                             (:bindings j) nil (when-let [subs (:subsumptions j)] {:subsumptions subs}))))))))

(defn- into-some
  "`(into to from)`, returning `to` itself when `from` is empty.  A placement gathers its
  seeds from nine sources and nearly every one is empty for an ordinary firing, where
  `into` would still take a transient and hand back a fresh vector per source."
  [to from]
  (if (seq from) (into to from) to))

(defn- variable-functor-consequent?
  "Does the rule consequent `consequent` apply a variable to arguments — `(?f ?x)`,
  under any wrapper `nm/applied-literals` descends?  The naming check a rule passes at
  assert time skips such a literal (docs/naming.md), so a firing that binds the variable
  forms a functor no check has read."
  [consequent]
  (boolean (some (fn [[_ lit]] (sx/variable? (first lit)))
                 (nm/applied-literals :consequent consequent))))

(defn- fact-violation
  "The violation that drops the fact conclusion `conseq` of `rule` in `pctx`, or nil when
  it is admissible: a naming violation where the rule's consequent has a variable functor
  (`special/naming-violation`), `adm`'s (`checks/constraint-admission` of the same
  sentence), the structural well-formedness of a special predicate the rule concluded,
  or a derived `genl` edge closing a taxonomy cycle through negation."
  [kb rule conseq pctx adm]
  (or (when (variable-functor-consequent? (:consequent rule))
        (special/naming-violation kb conseq pctx))
      (:violation adm)
      (special/wff-violation kb conseq pctx)
      (checks/edge-stratification-violation kb conseq)))

(defn- drop-fact-conclusion!
  "Drop the fact conclusion `conseq` for violation `v` and report it.  Returns the empty
  vector of new handles a placement that stored nothing returns."
  [kb rule conseq pctx v]
  (violations/report kb [(assoc v :sentence conseq :context pctx :rule (:rule-handle rule))])
  [])

(def ^:dynamic *witnesses*
  "nil, or a volatile `{:clock n :held {key value}}` that `place-nogoods!` binds for one
  call: the witnesses `subsumption-support` and `visibility-support` read, and the edge
  supporters' defeat classes, read while the change clock read `n`, keyed by what was
  read, the walk's scope (`tax/read-scope`) and the reading (`tax/*network-belief*`,
  `tax/*search*`).  An entry is answered
  only while the clock still reads `n`, so it equals a fresh read
  (`observe/note-change`); a placement pass reads every route of a family before it
  writes (`plan-sets`), and the nogoods of one family share their subsumptions."
  nil)

(defn- held
  "`(read)` for the key `k`, answered from the volatile `memo` (`*witnesses*`) while the
  change clock has not moved since it was held there, else read and held under the clock
  read before the read (`caches/held-if-settled`)."
  [memo k read]
  (let [clock (observe/change-clock)
        {c :clock m :held} @memo]
    (if-let [e (when (= c clock) (find m k))]
      (val e)
      (caches/held-if-settled
       read
       (fn [v]
         (vswap! memo (fn [{c :clock m :held}]
                        {:clock clock :held (assoc (if (= c clock) m {}) k v)}))
         v)))))

(defn- reading [] [tax/*network-belief* tax/*search*])

(defn- visibility-support
  "A witness for each context `pctx` had to see to hold the firing: the `genlCx` edge
  handles along one path per ingredient context (`tax/reach-support`), deduplicated where two
  ingredients share a stretch of the ancestor set.  A reflexive reach and a supporter with
  no recorded context rest on nothing and are skipped.  One path, one supporter per edge, as
  `subsumption-support` names one."
  [tax pctx ctxs]
  (if (every? #(or (nil? %) (= pctx %)) ctxs)
    []
    (into []
          (comp (remove #(or (nil? %) (= pctx %)))
                (distinct)
                ;; asked from the placement's own view, so a path it reads as hidden or
                ;; withdrawn is never the one named when another reaches
                (mapcat (fn [c]
                          (let [walk #(tax/reach-support tax :genlCx pctx c pctx)]
                            (if-let [memo *witnesses*]
                              (held memo [:genlCx pctx c (tax/read-scope tax :genlCx pctx) (reading)] walk)
                              (walk)))))
                (map first)
                (distinct))
          ctxs)))

;; ---- a nogood places its conclusions -------------------------------------

(def nogood-informant
  "The informant of every justification a placed nogood stores (`place-nogood!`)."
  exc/nogood-informant)

(defn- placement-witness?
  "Is the sentex at `h` a `genlCx` edge or a forced-monotonic declaration
  (`forced_monotonic_predicate`, `forced_monotonic_between_predicates`): an antecedent a
  placement reads beside its nogood's members and grounds?"
  [kb h]
  (contains? '#{genlCx forced_monotonic_predicate forced_monotonic_between_predicates}
             (nm/functor (:sentence (p/get-sentex (:records kb) h)))))

(defn- placement-justifications
  "The justifications under `nogood-informant` of the placed sentexes `hs` that `keep?`
  holds of, each with its `:core`: its antecedents but the `genlCx` edges and the
  forced-monotonic declarations (`placement-witness?`), the members and grounds of the nogood it places."
  [kb hs keep?]
  (let [tms (reasoning/tms kb)]
    (into []
          (comp (mapcat #(jtms/supports tms %))
                (distinct)
                (keep #(jtms/justification tms %))
                (filter #(and (= nogood-informant (:informant %)) (keep? %)))
                (map (fn [j] (assoc j :core (into #{} (remove #(placement-witness? kb %))
                                                  (:antecedents j))))))
          hs)))

(defn- nogood-justifications
  "The justifications under `nogood-informant` that rest on the nogood member `h`, each
  with its `:core` (`placement-justifications`).  The candidates are the placed
  `(contradicts …)` naming `h` and the `defeat`s naming one of their members, read off the
  term index, so the read does not grow with the firings that rest on `h`.  Given the
  member set `members`, the candidates are the `(contradicts …)` naming every member and
  the `defeat`s of the members, each one term-index intersection, so the read does not
  grow with the members' other nogoods."
  ([kb h] (nogood-justifications kb h nil))
  ([kb h members]
   (let [recs   (:records kb)
         idx    (:index kb)
         with   (fn [f keys] (filterv #(= f (some-> (p/get-sentex recs %) :sentence nm/functor))
                                      (reads/as-stored-with-terms idx keys)))
         handle-key sx/sentex-handle
         ctrs   (if members
                  (filterv #(= members (into #{} (map sx/handle-id)
                                             (rest (:sentence (p/get-sentex recs %)))))
                           (with 'contradicts (mapv handle-key members)))
                  (with 'contradicts [(handle-key h)]))
         defs   (into [] (comp (mapcat #(rest (:sentence (p/get-sentex recs %))))
                               (map sx/handle-id) (distinct)
                               (mapcat #(with sx/defeat-functor [(handle-key %) sx/defeat-functor])))
                      ctrs)]
     (placement-justifications kb (concat ctrs defs) #(some #{h} (:antecedents %))))))

(defn- placed-sentences
  "The sentences a nogood over `members` places, by `verdict` (`decide/verdict`):
  `(contradicts …)` naming the members in content order, and `(defeat (sentexHandle L))`
  for a unique weakest member `L`."
  [kb members verdict]
  (let [recs    (:records kb)
        ordered (nm/sort-by-content-key (fn [h] (let [s (p/get-sentex recs h)]
                                                  [(:sentence s) (:context s)]))
                                        members)]
    (cond-> [(apply list 'contradicts (map sx/sentex-handle ordered))]
      (map? verdict) (conj (list sx/defeat-functor (sx/sentex-handle (:defeat verdict)))))))

(defn- justify-placed!
  "Store `sentence` in `pctx` justified by `antes` under `informant` (`nogood-informant`
  unless given) at `:default`, carrying `bindings`, and return its handle when the record
  is new."
  ([kb sentence pctx antes] (justify-placed! kb sentence pctx antes nogood-informant {}))
  ([kb sentence pctx antes informant bindings]
   (let [tms        (reasoning/tms kb)
         recs       (:records kb)
         antes      (kb/antecedent-order kb antes)
         [h s new?] (kb/find-or-create-sentex kb sentence pctx)]
     (when new?
       (checks/force-sentex! kb s)
       (special/derived-sentex-added kb s h)
       ;; a new defeat moves its target's belief with no relabel of the target
       (special/recheck-defeat-target kb s))
     (jtms/ensure-node tms h (inc (long (reduce (fn [d a] (max (long d) (long (jtms/depth tms a))))
                                                0 antes))))
     (when-not (jtms/has-justification? tms informant antes h)
       (let [just (jtms/->just (p/next-id recs) informant antes h bindings :default)]
         (p/put-justification recs just)
         (jtms/add-justification tms just)))
     (when new? h))))

(defn- keyed-placements
  "The placement justifications `js`, each carrying its `:key` `[sentence context
  antecedents]`, as `{:jid :core :members :key}`: `:members` the handles of the nogood it
  places, which a `(contradicts …)` names and a `defeat` reads off the `contradicts`
  placed beside it in its context under the same antecedents, looked up by that pair.
  Two nogoods over one antecedent set keep apart by their members."
  [js]
  (let [named (fn [s] (into #{} (map sx/handle-id) (rest s)))
        ctrs  (group-by (fn [{[_ ctx antes] :key}] [ctx antes])
                        (filter #(= 'contradicts (nm/functor (first (:key %)))) js))]
    (into []
          (keep (fn [{[s ctx antes :as k] :key :as j}]
                  (let [ms (if (= 'contradicts (nm/functor s))
                             (named s)
                             (let [l (sx/handle-id (second s))]
                               (some (fn [{[s'] :key}]
                                       (let [ms (named s')] (when (contains? ms l) ms)))
                                     (get ctrs [ctx antes]))))]
                    (when ms {:jid (:id j) :core (:core j) :members ms :key k}))))
          js)))

(defn- placed-justifications
  "The justifications under `nogood-informant` resting on the handle `h`, each as `{:jid
  :core :members :key}` (`keyed-placements`), read off the term index
  (`nogood-justifications`).  Given `members`, only the nogood over exactly `members`."
  ([kb h] (placed-justifications kb h nil))
  ([kb h members]
   (let [recs (:records kb)]
     (keyed-placements
      (into [] (map (fn [j] (let [c (p/get-sentex recs (:consequence j))]
                              (assoc j :key [(:sentence c) (:context c) (set (:antecedents j))]))))
            (nogood-justifications kb h members))))))

(defn- placed-justifications-within
  "`placed-justifications` of the nogood over `members`, restricted to the contexts
  `within`.  While `within` holds fewer contexts than the term index holds sentexes
  naming a member, each context is probed for the `(contradicts …)` naming the members and
  the `defeat` of each member (`kb/find-sentex-handle`), so the read does not grow with the
  nogood's placements outside `within`; otherwise the term index read is filtered."
  [kb members within]
  (let [h (first members)]
    (if (< (count within) (count (reads/as-stored-naming-handle (:index kb) h)))
      (let [[ctr] (placed-sentences kb members nil)
            ss    (into [ctr] (map #(list sx/defeat-functor (sx/sentex-handle %))) members)]
        (keyed-placements
         (into [] (for [ctx within, s ss
                        :let [ph (kb/find-sentex-handle kb s ctx)]
                        :when ph
                        j (placement-justifications kb [ph] any?)]
                    (assoc j :key [s ctx (set (:antecedents j))])))))
      (filterv #(contains? within (second (:key %))) (placed-justifications kb h)))))

(def ^:private placement-hint-chunk
  "Items per prefetch hint of a placement loop (`placement-hinter`)."
  256)

(defn- placement-hinter
  "`(fn [items] …)` hinting the record store (`cap/prefetcher`) with the records the
  placement of the nogoods over the handles `(handles-of item)` reads: each handle, each
  stored sentex naming one (`reads/as-stored-naming-handle`: the placed `(contradicts …)` and `defeat`s
  among them), and the antecedents of their `nogood-informant` justifications.  nil when
  the store does not prefetch.  A loop over items hinted a chunk at a time
  (`cap/hinting`) fetches those records in one round trip a chunk rather than one a
  record."
  [kb handles-of]
  (when-let [pf (cap/prefetcher (:records kb))]
    (let [idx (:index kb)
          tms (reasoning/tms kb)]
      (fn [items]
        (let [hs     (into [] (comp (mapcat handles-of) (distinct)) items)
              placed (into [] (comp (mapcat #(reads/as-stored-naming-handle idx %)) (distinct)) hs)
              antes  (into [] (comp (mapcat #(jtms/supports tms %))
                                    (keep #(jtms/justification tms %))
                                    (filter #(= nogood-informant (:informant %)))
                                    (mapcat :antecedents))
                           placed)]
          (pf (into [] (distinct) (concat hs placed antes))))))))

(defn- membership-owned?
  "Is the placed nogood over `members` with antecedents but the `genlCx` edges `core` one
  the membership families place (`place-memberships!`): a ground among `core` supports a
  separation or cover declaration (`tax/separation-ends`), or the members are a
  membership and a denial of a strict supertype of its type (`membership/kind-of`)?"
  [kb members core]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (or (some (fn [h] (some #(tax/separation-ends tax %) (tax/supported-keys tax [h])))
                       (remove (set members) core))
                 (= :supertype (membership/kind-of (decide/unscoped-closures tax) (:records kb) members))))))

(defn- declared-members
  "`{member {declaration context}}`: each member of `members` forced-monotonic only by
  declarations outside the baseline set (`decide/literal-declarations`), with its
  declarations IN in the network, and defeasible in the network or denied by another
  member, since `decide/verdict` defeats that denial at any class.  Empty for almost every
  nogood."
  [kb members]
  (let [tax    (reasoning/taxonomy kb)
        tms    (reasoning/tms kb)
        recs   (:records kb)
        denied (into #{} (keep #(let [s (:sentence (p/get-sentex recs %))]
                                  (when (sx/negation? s) (second s))))
                     members)]
    (into {} (keep (fn [h]
                     (let [s (:sentence (p/get-sentex recs h))]
                       (when (or (strength/defeasible? (or (jtms/defeat-class tms h) :default))
                                 (contains? denied s))
                         (let [ds (into {} (filter #(jtms/network-in? tms (key %)))
                                        (some->> s (decide/literal-declarations tax)))]
                           (when (seq ds) [h ds]))))))
          members)))

(defn- subsets
  "The non-empty subsets of `xs`, smallest first."
  [xs]
  (sort-by count (rest (reduce (fn [ss x] (into ss (map #(conj % x)) ss)) [#{}] xs))))

(defn- choices
  "Every way to pick one `[declaration context]` per member of `ms` from `dm`, as vectors."
  [dm ms]
  (reduce (fn [cs m] (for [c cs, d (nm/sort-by-content-key (comp nm/print-key val) compare (dm m))]
                       (conj c d)))
          [[]] (sort ms)))

(defn- declared-placements
  "`[context antecedents verdict]` for the nogood over `members` with the declared members
  `dm` (`declared-members`), from the `[context antecedents]` `placements`.  Each placement
  keeps the baseline forced-monotonic verdict.  Each set of declarations whose verdict names
  a loser no smaller set names is a further placement, at the maximal contexts that see the
  placement and those declarations, resting on them (docs/nmtms.md, \"The forced-monotonic
  set\")."
  [kb dm placements verdict-of]
  (binding [tax/*network-belief* true]
    (let [tax    (reasoning/taxonomy kb)
          base-v (verdict-of #{})
          ms     (sort (keys dm))]
      (into []
            (mapcat
             (fn [[pctx antes]]
               (loop [ts (subsets ms) got {base-v [#{}]} out [[pctx antes base-v]]]
                 (if-let [t (first ts)]
                   (let [v (verdict-of t)]
                     (if (some #(every? t %) (got v))
                       (recur (rest ts) got out)
                       (recur (rest ts) (update got v (fnil conj []) t)
                              (if (map? v)
                                (into out
                                      (for [s    (choices dm t)
                                            :let [ctxs (cons pctx (map val s))]
                                            p    (res/exception-aware-placements
                                                  kb (into (vec antes) (map key) s) ctxs)]
                                        [p (-> (set antes) (into (map key) s)
                                               (into (visibility-support tax p ctxs)))
                                         v]))
                                out))))
                   out))))
            placements))))

(defn drop-justifications!
  "Drops each justification of `jids` from the network and the record store, and applies
  the removals the drops make (`integrate/apply-removals!`)."
  [kb jids]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (integrate/apply-removals!
     kb (reduce (fn [acc jid]
                  (let [r (jtms/drop-justification! tms jid)]
                    (p/delete-justification! recs jid)
                    (merge-with into acc r)))
                nil jids))))

(defn- place-justified!
  "Place the nogood over the handles `members` at each `[context antecedents]` of
  `placements`: `(contradicts …)` naming the members in content order, and, when
  `decide/verdict` over the members' classes names a unique weakest member `L`, `(defeat
  (sentexHandle L))`, each justified under `nogood-informant` at `:default`.  A member
  forced-monotonic only by a declaration adds the verdicts' placements
  (`declared-placements`).  Every justification an earlier placement of the same members
  stored under a core `owns?` that `placements` no longer gives is dropped.  Returns the
  handles it created.  With the context set `within`, only the placements in it are compared
  (`placed-justifications-within`)."
  ([kb members placements owns?] (place-justified! kb members placements owns? nil))
  ([kb members placements owns? within]
   (let [tms     (reasoning/tms kb)
         tax     (reasoning/taxonomy kb)
         recs    (:records kb)
         members (set members)
         global  (decide/global-reading tax)
         sentence #(:sentence (p/get-sentex recs %))
         verdict (fn [forced]
                   (decide/verdict #(or (jtms/defeat-class tms %) :default)
                                   #(boolean (or (contains? forced %)
                                                 (some-> (sentence %)
                                                         (as-> s (decide/forced-literal? tax s global)))))
                                   sentence members))
         dm      (declared-members kb members)
         entries (cond->> (if (empty? dm)
                            (let [v (verdict #{})] (map (fn [[pctx antes]] [pctx antes v]) placements))
                            (declared-placements kb dm placements verdict))
                   within (filter #(contains? within (first %))))
         want    (into #{} (for [[pctx antes v] entries, s (placed-sentences kb members v)]
                             [s pctx (set antes)]))
         have    (into {} (comp (filter #(and (= members (:members %)) (owns? (:core %))))
                                (map (juxt :jid :key)))
                       (if within
                         (placed-justifications-within kb members within)
                         (placed-justifications kb (first members) members)))
         gone    (into [] (keep (fn [[jid k]] (when-not (contains? want k) jid))) have)
         added   (nm/sort-by-content-key (fn [[s pctx]] [s pctx]) (remove (set (vals have)) want))
         _       (when (seq gone)
                   (drop-justifications! kb gone))
         made    (mapv (fn [[s pctx antes]] [s (justify-placed! kb s pctx antes)]) added)]
     (into [] (keep second) made))))

(defn place-nogood!
  "Place the nogood over the handles `members`, detected with the handles `grounds`, at each
  maximal context that sees the contexts they are stated in and where no except hides one
  (`res/exception-aware-placements`), each justified by the members, the grounds and the
  `genlCx` edges the placement sees them over (`visibility-support`; `place-justified!`).
  Returns the handles it created.  The caller states the nogood: every member IN.  `within`
  restricts the comparison (`special/drain-context-moves!`' `:reach`).  See docs/nmtms.md."
  ([kb members grounds] (place-nogood! kb members grounds nil))
  ([kb members grounds within]
   (let [tax  (reasoning/taxonomy kb)
         recs (:records kb)
         core (into (set members) grounds)
         ctxs (into [] (comp (map #(:context (p/get-sentex recs %))) (distinct)) core)]
     (place-justified! kb members
                       (for [pctx (cond->> (res/exception-aware-placements kb core ctxs)
                                    (and within (empty? (declared-members kb members)))
                                    (filter within))]
                         [pctx (into core (visibility-support tax pctx ctxs))])
                       #(= core %)
                       within))))

(defn- placed-members
  "The member sets the placed `(contradicts …)` sentexes among the handles `hs` name: a
  placement relabelled, as one does when a `genlCx` edge under it goes OUT, whose nogood
  its family places again where it stands."
  [kb hs]
  (when (pos? (reads/stored-count-with-functor (:index kb) 'contradicts))
    (let [tms  (reasoning/tms kb)
          recs (:records kb)]
      (into #{} (comp (filter (fn [h] (some #(= nogood-informant (:informant (jtms/justification tms %)))
                                            (jtms/supports tms h))))
                      (keep #(:sentence (p/get-sentex recs %)))
                      (filter #(= 'contradicts (nm/functor %)))
                      (map #(into #{} (keep sx/handle-id) (rest %))))
            hs))))

(defn- place-negations!
  "Place each negation pair (`place-nogood!`, no grounds) whose placement can have moved,
  and return the handles created: the pairs of the bodies `bodies` whose placement left
  (`negation/take-moved!`), of the bodies with a member among the handles `fresh` the pass
  relabelled or `placed` (`placed-members`), and of the bodies with a member stated in a
  context of `reach`'s `:below` (`special/drain-context-moves!`, `reads/as-stored-opposed-in`),
  which compares only its placements in `:under`.  Every body stored in both polarities when
  `first?` (`decide/take-edge-cursor!`) or the relation was rebuilt.  A pair is placed when both
  members are IN (`jtms/network-in?`).  Reads one count while no body is stored in both
  polarities."
  [kb bodies reach first? fresh placed]
  (when (reads/stores-opposed? (:index kb))
    (let [tms   (reasoning/tms kb)
          idx   (:index kb)
          full  (-> bodies
                    (into (negation/bodies-of kb fresh))
                    (into (negation/bodies-of kb placed)))
          [reached under]
          (cond (or first? (:all? reach)) [(reads/as-stored-opposed-bodies idx) nil]
                (nil? reach)              nil
                :else [(when (seq (:below reach))
                         (into #{} (remove full)
                               (negation/bodies-of kb (reads/as-stored-opposed-in idx (:below reach)))))
                       (:under reach)])
          full  (cond-> full (nil? under) (into reached))]
      (let [pairs (nm/sort-by-content-key
                   (fn [[pair]] (into [] (mapcat #(let [s (p/get-sentex (:records kb) %)]
                                                    [(:sentence s) (:context s)]))
                                      pair))
                   (concat (map vector (negation/pairs kb full))
                           (when under
                             (map #(vector % under) (negation/pairs kb reached)))))]
        (with-open [r (progress/start ::place-negations "settle: place the negation pairs" (count pairs))]
          (into []
                (comp (filter (fn [[[n q]]] (and (jtms/network-in? tms n) (jtms/network-in? tms q))))
                      (mapcat (fn [[[n q] within]]
                                (if (exc/edge-read-only? tms q)
                                  (place-justified! kb #{n q} [] #(= #{n q} %))
                                  (place-nogood! kb #{n q} #{} within)))))
                (progress/each r pairs)))))))

;; ---- a placement climbs the genl edges a match subsumed through --------

(defn- subsumption-links
  "The `[sub super]` predicate pairs a firing reached through predicate/type subsumption:
  one per matched fact that did not satisfy its antecedent on the antecedent's own key.  Both
  sides are `rules/antecedent-key`s (a functor or `[:not functor]`), which carry the polarity:
  a positive fact is on a spec of a positive antecedent, so the fact is the sub; a negated fact
  is on a genl of a negated antecedent (`res/match1`), so the antecedent's body is the sub.  A
  `genl` antecedent answered from the closure (`solve-closure`) records its pair on `:matched`
  as `[key nil [sub super]]`.  Empty for an ordinary firing.  `record-of` is the firing's
  fetched records; a matched handle with no record is skipped.  Read upward from the sub
  (the up-closure of a term is its chain to `thing`; the down-closure of a general antecedent
  can be most of the hierarchy), through the global closure: whether two predicates are
  related is a property of the KB, and which contexts see the relating edges is
  `subsumption-support`'s question.  Polarity does not cross: a key of one polarity against a
  key of the other is a plain unify and gives no link."
  [kb matched record-of]
  (if (not-any? (fn [[ak h link]]
                  (or link
                      (when-let [s (:sentence (record-of h))]
                        (not= ak (rules/antecedent-key s)))))
                matched)
    ;; the ordinary firing, settled in one pass before a pipeline is built for it
    []
    (let [tax (reasoning/taxonomy kb)]
      (into []
            (comp (keep (fn [[ak h link]]
                          ;; a closure link (`solve-closure`) names its pair outright
                          (or link
                              (when-let [s (:sentence (record-of h))]
                                (let [fk (rules/antecedent-key s)]
                                  (when (not= ak fk)
                                    (cond
                                      ;; positive: the fact is on a spec of the antecedent
                                      (and (symbol? ak) (symbol? fk)) [fk ak]
                                      ;; negated: contravariant, so the antecedent is the spec
                                      (and (vector? ak) (vector? fk)) [(second ak) (second fk)])))))))
                  (distinct)
                  (keep (fn [[sub super :as link]]
                          (if (contains? (tax/genls-global tax sub) super)
                            link
                            ;; reached across `genlInverse` edges: the link carries the
                            ;; parity the match was read at, which its witness walks
                            (let [[st sw] (tax/signed-closure tax :up sub nil)]
                              (cond (contains? st super) [sub super false]
                                    (contains? sw super) [sub super true])))))
                  ;; a `[sub super swapped?]` link reached both ways is one subsumption
                  (distinct))
            matched))))

(defn- link-witness
  "The `[handle ctx]` supporters of one path for the subsumption `link`, `[sub super]`
  through `genl` edges or `[sub super swapped?]` through the signed closure, that
  `vantage` sees, widest-bottleneck under `supporter-class` over the classes `thresholds`;
  nil when it sees none.  A `genl` link reads the route lengths held in `router`
  (`tax/reach-support`)."
  [tax [sub super :as link] vantage supporter-class thresholds router]
  (if (= 2 (count link))
    (tax/reach-support tax :genl sub super vantage supporter-class thresholds router)
    (tax/signed-reach-support tax sub super (nth link 2) vantage supporter-class)))

(defn- strict-witness
  "`link-witness` under `holding`, `res/holding-class`, kept only when `holding` reads
  every supporter on it `:monotonic`, so a `genl` link's walk takes no weaker edge.  The
  witness of a contrapositive link: a negated match and a membership beside a denial of a
  supertype read an edge's contrapositive, and a `:default` edge does not contrapose
  (docs/inference.md)."
  [tax link vantage holding router]
  (when-let [hs (link-witness tax link vantage holding [:monotonic] router)]
    (when (every? #(= :monotonic (holding (first %))) hs) hs)))

(defn- negated-links
  "The set of the `links` (`subsumption-links` of `matched`) a negated literal climbed,
  each an edge's contrapositive, or nil."
  [kb matched record-of links]
  (when (seq links)
    (not-empty (set (subsumption-links kb (filterv #(vector? (first %)) matched) record-of)))))

(defn- subsumption-support
  "A witness for each of a firing's subsumptions, as `[handle ctx]` supporter pairs
  (`tax/reach-support`), or nil when `vantage` sees no path for one of them.  A nil `vantage`
  asks globally, as placement does: the supporters' contexts feed
  `maximal-common-descendant-contexts` beside the rule's and the facts', so every placement
  sees every edge.  The join itself stays global (`complete-antecedents`): narrowing it would
  drop firings that placement accepts.  A link in the set `strict` is a contrapositive one, witnessed by a path
  every edge of which `res/holding-class` reads `:monotonic`, else nil (`strict-witness`)."
  [kb links vantage strict]
  ;; the widest-bottleneck route: a firing that climbed the genl closure rests on the
  ;; strongest path, so its conclusion is capped at that path's floor; `supporter-class` is
  ;; the live JTMS defeat class of each edge supporter
  (let [memo  *witnesses*
        tms   (reasoning/tms kb)
        supporter-class (if memo
                          (fn [h] (held memo [:class h] #(jtms/defeat-class tms h)))
                          #(jtms/defeat-class tms %))
        strict-class (when (seq strict) (res/holding-class kb))
        ;; the route lengths of every walk under one class reading, held beside the
        ;; witnesses while the clock holds; a walk reading an open route question holds
        ;; nothing (`caches/*open-mark*`)
        router (fn [k] (when (and memo (nil? caches/*open-mark*))
                         (held memo [:router k (reading)] #(java.util.HashMap.))))
        walk  (fn [link]
                (if (contains? strict link)
                  (strict-witness (reasoning/taxonomy kb) link vantage strict-class (router :strict))
                  (link-witness (reasoning/taxonomy kb) link vantage supporter-class
                                [:monotonic :default] (router :class))))
        ;; a `genlInverse` link's witness also reads the flat cache, which the `genl`
        ;; read scope does not key, so only a `genl` link is held
        read  (if memo
                (let [scope (tax/read-scope (reasoning/taxonomy kb) :genl vantage)]
                  (fn [link] (if (= 2 (count link))
                               (held memo [(if (contains? strict link) :genl-strict :genl)
                                           link scope (reading)]
                                     #(walk link))
                               (walk link))))
                walk)]
    (reduce (fn [acc link]
              (if-let [hs (read link)]
                (into acc hs)
                (reduced nil)))
            []
            links)))

(defn- descent-placements
  "`{placement [edge-handle …]}` for a subsumed firing whose conclusion descends below the
  contexts that see the rule and the facts: one entry per maximal context that sees the
  ingredients and every edge of one witness combination.  Every combination no other covers
  is placed (`tax/reach-supports`, `tax/uncovered`); a placement two combinations decide names
  the first in content order.  nil when some subsumption has no route (read unscoped).  With
  the context set `within`, only the placements in it.  Routes and supporter classes are held
  in `*witnesses*` while it is bound.  A link in `strict` takes only routes `res/holding-class`
  reads `:monotonic` on every edge."
  [kb links ingredients within strict]
  (let [tax      (reasoning/taxonomy kb)
        tms      (reasoning/tms kb)
        memo     *witnesses*
        class-of (if memo
                   (fn [h] (held memo [:class h] #(jtms/defeat-class tms h)))
                   #(jtms/defeat-class tms %))
        rank     #(strength/rank-of (or (class-of %) :default))
        holding  (when (seq strict) (res/holding-class kb))
        walk     (fn [[sub super :as link]]
                   (let [s?  (contains? strict link)
                         cls (if s? holding class-of)
                         rs  (if (= 2 (count link))
                               (tax/reach-supports tax :genl sub super nil cls nil (when s? :monotonic))
                               ;; one route across `genlInverse` edges: the fewest of them
                               (when-let [r (tax/signed-reach-support tax sub super (nth link 2) nil cls)]
                                 [r]))]
                     (if s?
                       (filterv (fn [r] (every? #(= :monotonic (holding (first %))) r)) rs)
                       rs)))
        per-link (mapv (if memo
                         (fn [link] (if (= 2 (count link))
                                      (held memo [(if (contains? strict link) :genl-strict-routes :genl-routes)
                                                  link (reading)]
                                            #(walk link))
                                      (walk link)))
                         walk)
                       links)]
    (when (every? seq per-link)
      (let [combos (reduce (fn [acc routes] (vec (for [x acc, r routes] (into x r))))
                           [[]] per-link)
            combos (tax/uncovered tax
                                  (fn [hs] [(reduce min Long/MAX_VALUE (map (comp rank first) hs))
                                            (tax/context-floor tax (map second hs))])
                                  combos)]
        (reduce (fn [m hs]
                  (let [ectxs (concat ingredients (keep second hs))
                        ehs   (mapv first hs)]
                    (reduce (fn [m p]
                              (if (contains? m p)
                                m
                                (assoc m p (into ehs (visibility-support tax p ectxs)))))
                            m
                            (nm/sort-by-content-key
                             nm/print-key compare
                             (cond->> (tax/maximal-common-descendant-contexts tax ectxs)
                               within (filter within))))))
                {} combos)))))

(defn- placements-over*
  "`placements-over` under the network reading it binds."
  [kb links supporters ingredients within strict]
  (let [tax  (reasoning/taxonomy kb)
        ;; with `links`, a descent placement reads every candidate's path, so
        ;; `placements-over` filters the candidates' answer instead
        base (cond->> (res/exception-aware-placements kb supporters ingredients)
               (and within (empty? links)) (filterv within))]
    (if (empty? links)
      ;; no subsumption to witness, so the whole support map is the visibility one —
      ;; and it is empty for the firing whose rule and facts are where the conclusion
      ;; lands, which is nearly all of them
      [base (reduce (fn [m b]
                      (let [vs (visibility-support tax b ingredients)]
                        (if (seq vs) (assoc m b vs) m)))
                    {} base)]
      (let [seeing (reduce (fn [m b]
                             (if-let [hs (subsumption-support kb links b strict)]
                               (assoc m b (into (mapv first hs)
                                                (visibility-support
                                                 tax b (concat ingredients (keep second hs)))))
                               m))
                           {} base)]
        (if (and (seq seeing) (= (count seeing) (count base)))
          ;; `seeing` is the placement filter as well as the support map, and a
          ;; subsumed firing always names at least one `genl` edge, so no entry of it
          ;; is empty and the two readings cannot disagree
          [(filterv seeing base) seeing]
          (let [;; a descent placement at or below a candidate that sees a path of its
                ;; own reads that candidate's conclusion already
                descent (into {}
                              (remove (fn [[p _]] (some #(tax/sees? tax p %) (keys seeing))))
                              (descent-placements kb links ingredients within strict))]
            (when (or (seq seeing) (seq descent))
              [(into (filterv seeing base)
                     (nm/sort-by-content-key nm/print-key compare (keys descent)))
               (merge descent seeing)])))))))

(defn- placements-over
  "`placement-ingredients`' answer for the `genl` subsumptions `links`, the supporter
  handles `supporters` and their contexts `ingredients`: `[placement-contexts
  {placement-context [edge-handle]}]`, or nil when no context places them.  The candidates
  are the maximal contexts that see every supporter where no except hides one
  (`res/exception-aware-placements`).  A placed nogood (`route-placements`) and a guard defeat
  (`guard-defeat-placements`) read it with their own supporters.  Every witness search reads
  the network and the stored `except`s and no placed `defeat` (`tax/*network-belief*`).  With
  `within`, only the placements in it; with no `links`, only those placements' support.  A
  link in `strict` is witnessed only by a path held at `:monotonic` (`strict-witness`)."
  ([kb links supporters ingredients] (placements-over kb links supporters ingredients nil nil))
  ([kb links supporters ingredients within] (placements-over kb links supporters ingredients within nil))
  ([kb links supporters ingredients within strict]
   (binding [tax/*network-belief* true]
     (cond-> (placements-over* kb links supporters ingredients within strict)
       (and within (seq links)) (some-> (update 0 #(filterv within %)))))))

;; ---- a guard that holds below the placement places a defeat ---------------

(def guard-informant
  "The informant of every justification a guard defeat stores (`place-guard-defeats!`)."
  exc/guard-informant)

(defn- block-conditions
  "The block conditions of the rule `rsx` at `rh`, each as `[conjuncts handles]`: every
  believed `exceptWhen` of the rule with its meta-sentex's handle, wherever it is stated,
  and each `unknown` antecedent's query with none."
  [kb rh rsx]
  (-> (into [] (map (fn [{:keys [handle query]}] [query #{handle}]))
            (when (reads/watched-rule? (:index kb) rh) (provers/rule-exception-entries kb rh)))
      (into (map (fn [u] [(sx/naf-query-conjuncts u) #{}])) (rules/naf-antecedents rsx))))

(defn- grant-supported
  "The guard `solutions` of a condition whose conjuncts include the closed-extent
  negatives `ce`, which the join withholds (`join-order`).  For each literal ground under
  a solution, the solution is taken once per handle that answers the literal alone, a
  grant or a stored negative, with that handle added (`provers/closed-extent-supports`,
  read in the network), so a defeat or an except of the grant takes the guard defeat
  resting on it out of force at a reader.  A literal another prover answers, or no grant
  covers, leaves the solution as it is."
  [kb ce solutions]
  (if (empty? ce)
    solutions
    (binding [tax/*network-belief* true]
      (reduce (fn [sols l]
                (into [] (mapcat (fn [s]
                                   (let [g (res/substitute l (:bindings s))]
                                     (if-let [gs (when (empty? (sx/free-vars g))
                                                   (provers/closed-extent-supports kb g))]
                                       (map #(update s :handles conj %) gs)
                                       [s]))))
                      sols))
              (vec solutions) ce))))

(defn- guard-solutions
  "The solutions of the block condition `conds` under `bindings`, as the join's
  `{:bindings :handles :matched}` states: the forward join over its conjuncts (`solve-rule`),
  a `thereExists` contributing its body.  A conjunct a prover answers from stored facts names
  the facts it read.  An `unknown` binds nothing and passes through.  The conjuncts are
  rewritten to the normal form of each reader at or below `pctx` whose election can differ
  (`special/reader-contexts-at`, `provers/condition-normalizer`) and the join runs once per
  distinct form.  A closed-extent negative conjunct names the grant or stored negative its
  answer rests on (`grant-supported`).  `cpred` is the rule's consequent functor."
  [kb conds bindings pctx cpred]
  (let [flat  (fn flat [cs] (mapcat #(if (sx/there-exists? %) (flat (sx/conjuncts (nth % 2))) [%]) cs))
        goals (mapv #(res/substitute % bindings) (flat conds))
        ctxs  (or (seq (special/reader-contexts-at kb pctx (apply list 'and goals))) [pctx])
        forms (distinct (for [c ctxs :let [norm (or (provers/condition-normalizer kb c) identity)]]
                          (mapv #(sx/canon (norm %)) goals)))]
    (distinct (mapcat #(grant-supported kb (closed-extent-antecedents kb %) (solve-rule kb % bindings cpred))
                      forms))))

(defn- guard-conditions-of
  "`block-conditions` read off the chainer's rule fields (`rule-fields-of`)."
  [rule]
  (-> (into [] (map (fn [{:keys [handle query]}] [query #{handle}])) (:excepts rule))
      (into (map (fn [u] [(sx/naf-query-conjuncts u) #{}])) (:naf rule))))

(defn- blocker-support-hiders
  "The excepts and defeats naming a handle of the support, past premises, of a defeat
  naming a handle of `blk`, all read off the index (`reads/as-stored-naming`), leaving out
  those defeats themselves and the defeats of the guarded conclusion `f`.  At a reader
  that sees one, it can lower a member's class, or hide a member, a ground or the defeat,
  and so take the defeat out of force and leave the blocker believed there."
  [kb blk f]
  (let [idx (:index kb)]
    (when (reads/stores-any? idx sx/defeat-functor)
      (let [tms   (reasoning/tms kb)
            ds    (into #{} (mapcat #(reads/as-stored-naming idx sx/defeat-functor %)) blk)
            sup   (into #{} (mapcat #(exc/support tms % (constantly false) true)) ds)
            own   (into ds (reads/as-stored-naming idx sx/defeat-functor f))
            named #(into #{} (mapcat (fn [h] (reads/as-stored-naming idx % h))) sup)]
        (into (named sx/except-functor) (remove own) (named sx/defeat-functor))))))

(defn- guard-solution-placements
  "`[[q blockers] …]` for the block conditions `conds` (`block-conditions`' shape) of a
  firing whose conclusion F is placed in `pctx`, under the settled bindings `b`.  For each
  solution read with no context (`guard-solutions`), each context `placements-over` gives for
  the handles it read, with the `genl` pairs its match climbed (`subsumption-links`, a negated
  one witnessed at `:monotonic` only, `negated-links`), where the condition holds through the
  excepts (`provers/exception-holds?` under `tax/*network-belief*`).  A placement at `pctx` is
  kept whatever class its blockers take.  `blockers` is the
  solution's handles, the `exceptWhen`'s own handle and the edges `placements-over` names.
  Each except or defeat that can take a blocker's defeat out of force
  (`blocker-support-hiders`) is one more supporter.  A condition `pctx` sees that holds with no
  placement it sees is placed at `pctx` on the condition's own handle
  (`place-guard-defeats!`).  `cpred` is the rule's consequent functor."
  [kb conds b pctx f cpred]
  (let [rec    #(p/get-sentex (:records kb) %)
        tax    (reasoning/taxonomy kb)
        holds? (fn [conds q] (binding [tax/*network-belief* true]
                               (provers/exception-holds? kb conds b q)))
        placed (fn [conds links strict blk]
                 (let [ctxs   (into [pctx] (comp (keep #(:context (rec %))) (distinct)) blk)
                       [ps m] (placements-over kb links blk ctxs nil strict)]
                   (into [] (comp (filter #(holds? conds %))
                                  (map (fn [q] [q (into blk (get m q))])))
                         ps)))]
    (mapcat
     (fn [[cs hs]]
       (let [pls (for [{sup :handles matched :matched}
                       (distinct (map #(select-keys % [:handles :matched])
                                      (guard-solutions kb cs b pctx cpred)))
                       :let [blk    (into hs sup)
                             links  (subsumption-links kb matched rec)
                             strict (negated-links kb matched rec links)
                             base   (placed cs links strict blk)
                             bctxs  (mapv first base)]
                       pl (into base
                                (comp (mapcat #(placed cs links strict (conj blk %)))
                                      (remove (fn [[q]] (some #(tax/sees? tax q %) bctxs))))
                                (blocker-support-hiders kb blk f))]
                   pl)]
         ;; a condition `pctx` sees that holds there through a prover naming no stored
         ;; fact (a `reflexive` self-pair, an `argIsa` type) gives no placement `pctx`
         ;; sees, and its defeat rests on the condition's own handle alone
         (if (and (not-any? (fn [[q]] (tax/sees? tax pctx q)) pls)
                  (every? #(res/rule-visible-from? kb pctx (:context (rec %))) hs)
                  (holds? cs pctx))
           (conj (vec pls) [pctx hs])
           pls)))
     conds)))

(defn- different-guard-placements
  "`[[q blockers] …]` for the `(different …)` antecedents of the rule `rsx`, of a firing
  placed in `pctx` under the settled bindings `b`: each context `q` where an antecedent fails,
  with the handles it fails on.  Two arguments a reader joins (`special/reader-contexts-at`)
  give one blocker set per supporter choice along one path
  (`tax/scoped-path-supporters`), or the visible equalities bearing on the pair for a compound
  argument (`special/bearing-equalities`); each statement making an argument indeterminate is
  a set of its own (`provers/indeterminacy-supports`).  `placements-over` places each set."
  [kb rsx b pctx]
  (let [tax (reasoning/taxonomy kb)
        rec #(p/get-sentex (:records kb) %)]
    (binding [tax/*network-belief* true]
      (into []
            (distinct)
            (for [d     (rules/different-antecedents rsx)
                  :let  [g    (res/substitute d b)
                         args (vec (rest g))
                         pair (fn [r]
                                (let [vis (res/visible-supporter-fn kb r)]
                                  (for [i (range (count args)), j (range (inc i) (count args))
                                        :let [x (nth args i), y (nth args j)]
                                        blk (if (and (symbol? x) (symbol? y))
                                              (some-> (tax/scoped-path-supporters tax x y vis)
                                                      tax/path-alternatives)
                                              (some-> (into (sorted-set) (filter vis)
                                                            (special/bearing-equalities kb (list 'different x y)))
                                                      not-empty vector))]
                                    blk)))]
                  blk   (distinct (concat (mapcat pair (remove #{pctx} (special/reader-contexts-at kb pctx g)))
                                          (for [t args, m (provers/indeterminacy-supports kb t)] #{m})))
                  :let  [[ps sm] (placements-over kb [] blk
                                                  (into [pctx] (comp (keep #(:context (rec %))) (distinct)) blk))]
                  q     ps
                  :when (empty? (provers/solve-goal kb g q))]
              [q (into blk (get sm q))])))))

(defn- closed-extent-guard-placements
  "`[[q blockers] …]` for the closed-extent negative antecedents `ce` of a firing whose
  conclusion F is placed in `pctx`, under the settled bindings `b`: each context `q` below
  `pctx` where an antecedent `(not L)` fails at level 6.  `L` blocks as an `(unknown L)`
  condition does (`guard-solution-placements`), at each context where `(not L)` fails.  A
  set of excepts and defeats naming the grants `pctx` sees (`provers/closed-extent-supports`),
  one per grant, blocks at each context `placements-over` gives it where no other answer of
  `(not L)` is visible.  `cpred` is the rule's consequent functor."
  [kb ce b pctx f cpred]
  (let [idx    (:index kb)
        rec    #(p/get-sentex (:records kb) %)
        member (fn [l]
                 (remove (fn [[q]] (binding [tax/*network-belief* true]
                                     (provers/exception-holds? kb [l] b q)))
                         (guard-solution-placements kb [[[(second l)] #{}]] b pctx f cpred)))
        hiders (fn [g] (nm/sort-by-content-key identity (concat (reads/as-stored-naming idx sx/except-functor g)
                                                                (reads/as-stored-naming idx sx/defeat-functor g))))
        hidden (fn [l]
                 (let [sups   (provers/closed-extent-supports kb (res/substitute l b))
                       grants (filterv #(and (not (rules/negative-literal? (:sentence (rec %))))
                                             (res/supporter-visible? kb % pctx false))
                                       sups)]
                   (when (seq grants)
                     (for [blk   (reduce (fn [bs g] (for [s bs, h (hiders g)] (conj s h))) [#{}] grants)
                           :let  [[ps sm] (placements-over kb [] blk
                                                           (into [pctx] (comp (keep #(:context (rec %))) (distinct)) blk))]
                           q     ps
                           :when (every? (set grants) (filter #(res/supporter-visible? kb % q false) sups))]
                       [q (into blk (get sm q))]))))]
    (into []
          (comp (remove (fn [[q]] (= q pctx))) (distinct))
          (concat (mapcat member ce)
                  (binding [tax/*network-belief* true] (doall (mapcat hidden ce)))))))

(defn- mention-guard-placements
  "`[[q blockers] …]` for the antecedents of `rsx` a firing placed in `pctx` under `b`
  reads through a mention probe alone (`probed-only?`): each context below `pctx` that
  `placements-over` gives a declaration typing the mention (`res/mention-declarations`)
  and `pctx`, where the antecedent has no believed match, blocked by that declaration."
  [kb rsx b pctx]
  (let [tax (reasoning/taxonomy kb)
        tms (reasoning/tms kb)]
    (binding [tax/*network-belief* true]
      (doall
       (for [[g] (mention-read kb (:antecedent rsx) b (constantly nil))
             :when (probed-only? kb g pctx)
             n   (range 1 (count g))
             :when (seq? (nth g n))
             d   (res/mention-declarations kb tax (first g) n)
             :let [[ps sm] (placements-over kb [] #{(:id d)} [pctx (:context d)])]
             q   ps
             :when (and (not= q pctx)
                        (not-any? (fn [[h]] (jtms/in? tms h)) (res/matches-visible kb g q)))]
         [q (into #{(:id d)} (get sm q))])))))

(defn- guard-defeat-placements
  "`#{[context antecedents]}`: where the firing `j`, a justification record of a rule,
  owes a guard defeat of its conclusion F (`guard-solution-placements`,
  `different-guard-placements`, `closed-extent-guard-placements`,
  `mention-guard-placements`).  F's own context is among
  them when a blocker blocks F there, whatever the blockers' class.  The antecedents are the
  blockers, the firing's rule and antecedents, and F.  `given` is `block-conditions`'
  answer, when the caller holds it."
  [kb j given]
  (let [recs (:records kb)
        rh   (:informant j)
        f    (:consequence j)
        rsx  (when (integer? rh) (p/get-sentex recs rh))
        pctx (:context (p/get-sentex recs f))]
    (if-not (and pctx rsx (rules/rule? rsx))
      #{}
      (let [core (-> (set (:antecedents j)) (conj rh f))
            b    (settled-bindings kb (:bindings j) pctx)]
        (into #{}
              (map (fn [[q hs]] [q (into core hs)]))
              (concat (guard-solution-placements kb (or given (block-conditions kb rh rsx))
                                                 b pctx f (nm/functor (:consequent rsx)))
                      (when (rules/has-different? rsx)
                        (different-guard-placements kb rsx b pctx))
                      (when-let [ce (seq (redecided-negative-antecedents kb rsx))]
                        (closed-extent-guard-placements kb ce b pctx f (nm/functor (:consequent rsx))))
                      (mention-guard-placements kb rsx b pctx)))))))

(defn- inheritance-defeat-placements
  "`#{[context antecedents]}`: the defeats of the conclusion F of the firing `j` that the
  `:default` contrary claims of its inherited antecedents owe (`inherited-goals`,
  `inherit/contraries`), each at F's context, resting on one contrary claim, the firing's
  rule and antecedents, and F.  Read in the network and through the
  excepts.  A `:monotonic` contrary withdraws the firing instead
  (`inheritance-withdrawn?`)."
  [kb j]
  (let [recs (:records kb)
        rh   (:informant j)
        f    (:consequence j)
        rsx  (when (integer? rh) (p/get-sentex recs rh))
        pctx (:context (p/get-sentex recs f))]
    (if-not (and pctx rsx (rules/rule? rsx)
                 (some #(declaration-record? (p/get-sentex recs %)) (:antecedents j)))
      #{}
      (let [gs (inherited-goals kb rsx (delay (settled-bindings kb (:bindings j) pctx)) pctx)]
        (if (empty? gs)
          #{}
          (let [core (-> (set (:antecedents j)) (conj rh f))]
            (binding [tax/*network-belief* true
                      inherit/*memo*       nil]
              (into #{}
                    (for [g gs
                          c (inherit/contraries kb g pctx)
                          :when (= :default (:class c))]
                      [pctx (conj core (:handle c))])))))))))

(defn- edge-reading-defeat-placements
  "`#{[context antecedents]}`: the defeats of the edge reading F that the
  `exc/edge-reading-informant` justification `j` concludes owes, one for each stored
  denial of F's sentence, at each maximal context that sees F and the denial where no
  except hides one, resting on the denial, `j`'s antecedents and F.  A denial of either
  strength undercuts the reading (docs/inference.md, \"An edge's reading\")."
  [kb j]
  (if (not= exc/edge-reading-informant (:informant j))
    #{}
    (let [recs (:records kb)
          f    (:consequence j)
          fsx  (p/get-sentex recs f)]
      (if-not fsx
        #{}
        (let [core (conj (set (:antecedents j)) f)]
          (into #{}
                (for [d   (reads/as-stored-at-path (:index kb) [:false (sx/canon (:sentence fsx)) '?c])
                      :let [dsx (p/get-sentex recs d)]
                      :when dsx
                      q   (res/exception-aware-placements kb #{f d} [(:context fsx) (:context dsx)])]
                  [q (conj core d)])))))))

(defn- rule-firing-blocked?
  "Is a firing of the rule `rsx`, settled bindings `bindings` (a delay), placed in `pctx`,
  blocked by something the rule carries: a `(different …)` antecedent a merge or an
  indeterminacy withdrew, a closed-extent negative antecedent that no longer holds, an
  aggregate or computed antecedent whose answer moved, a `disjoint` antecedent `pctx` no
  longer reads separated or a negated one it no longer reads denied (`separation-exempted?`),
  an inherited antecedent a more specific `:monotonic` claim undercut, a qualitative
  network that became unsatisfiable or no longer admits a typed antecedent's arguments, or
  an antecedent `pctx` reads at a mention (`mention-unread?`)?  An `exceptWhen` or
  `(unknown S)` that holds blocks nothing here (`place-guard-defeats!`).  Read in the
  conclusion's context, uncached; a placed and a refused firing both come here."
  [kb rsx bindings pctx]
  (boolean
   (or (when (rules/has-different? rsx)
         (different-blocks? kb (rules/different-antecedents rsx) @bindings pctx))
       (when-let [ce (seq (redecided-negative-antecedents kb rsx))]
         (closed-extent-blocks? kb ce @bindings pctx))
       (post-join-withdrawn? kb rsx bindings pctx)
       (computed-withdrawn? kb rsx bindings pctx)
       (when (some #(or (separation-literal? %) (separation-denial-antecedent? kb %))
                   (:antecedent rsx))
         (separation-exempted? kb (:antecedent rsx) @bindings pctx))
       (inheritance-withdrawn? kb rsx bindings pctx)
       (entailment-withdrawn? kb rsx bindings pctx)
       (mention-unread? kb (:antecedent rsx) @bindings pctx))))

(defn- lazy-membership-types
  "The types `T` of the facts `(T x)` of `facts` beside which a firing proving a
  lazy-forward literal (`facts` holds a lazy-forward rule's record) concludes the
  membership `conclusion`, `(C x)`; nil for any other firing or conclusion
  (`unrestated-placements`)."
  [conclusion facts]
  (when (and (seq? conclusion) (= 2 (count conclusion)) (not= sx/not-functor (first conclusion))
             (some #(some-> % rules/lazy-sentex?) facts))
    (let [x (second conclusion)]
      (seq (keep (fn [f] (let [s (:sentence f)]
                           (when (and (seq? s) (= 2 (count s)) (= x (second s))
                                      (symbol? (first s)) (not= sx/not-functor (first s)))
                             (first s))))
                 facts)))))

(defn- lazy-firing-blocked?
  "Does justification `j`, concluding `csx` in `pctx` under the rule informant `inf`, rest
  on a lazy-forward rule `offerable-lazy?` refuses, which a forward join proves nothing by,
  conclude a membership `pctx`'s taxonomy holds from a fact it rests on
  (`unrestated-placements`), or prove a lazy literal by the converse of its reader's lazy
  reading in `pctx` (`converse-lazy-reading?`)?  Reads no record on a store holding no
  lazy-forward rule (`kb/stores-lazy-rule?`)."
  [kb j csx pctx inf]
  (when (kb/stores-lazy-rule? kb)
    (let [recs (into [] (keep #(p/get-sentex (:records kb) %)) (jtms/rests-on j))
          lz   (filterv rules/lazy-sentex? recs)]
      (and (seq lz)
           (or (boolean (some #(not (offerable-lazy? kb %)) lz))
               (when-let [ts (lazy-membership-types (:sentence csx) recs)]
                 (let [c (first (:sentence csx)), tx (reasoning/taxonomy kb)]
                   (boolean (some #(contains? (tax/genls tx % pctx) c) ts))))
               (when (special/firing-informant? kb inf)
                 (when-let [rsx (p/get-sentex (:records kb) inf)]
                   (converse-lazy-reading? kb (nm/functor (:sentence csx)) (:antecedent rsx) lz pctx))))))))

(defn justification-excepted?
  "Is justification `j` currently blocked — by a visibility `except` hiding one of its
  antecedents, by a lazy-forward rule it rests on that no join reads or that it reads as
  its own converse (`lazy-firing-blocked?`), or by anything its rule carries
  (`rule-firing-blocked?`)?

  The conclusion's record names the placement context every check is evaluated in, and
  the informant names the rule."
  [kb j]
  (boolean
   (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
     (let [pctx (:context csx)
           inf  (:informant j)]
       (or (antecedent-hidden? kb (let [b (exc/belief-only-antecedent j)]
                                    (cond->> (jtms/rests-on j) b (remove #{b})))
                               pctx)
           (lazy-firing-blocked? kb j csx pctx inf)
           (when (special/firing-informant? kb inf)
             (when-let [rsx (p/get-sentex (:records kb) inf)]
               (rule-firing-blocked? kb rsx
                                     (delay (settled-bindings kb (:bindings j) pctx))
                                     pctx))))))))

(defn- guard-justifications
  "`{jid [sentence context antecedents]}`: the justifications under `guard-informant`
  resting on the conclusion of the firing `j` that `j` owns (`exc/guard-owners`, read
  among `j` and the other justifications of the conclusion)."
  [kb j]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        js   (into [j] (comp (remove #{(:id j)}) (keep #(jtms/justification tms %)))
                   (jtms/supports tms (:consequence j)))]
    (into {}
          (comp (keep #(jtms/justification tms %))
                (filter #(= guard-informant (:informant %)))
                (keep (fn [g] (when (contains? (exc/guard-owners recs g js) (:id j))
                                (let [c (p/get-sentex recs (:consequence g))]
                                  [(:id g) [(:sentence c) (:context c) (set (:antecedents g))]])))))
          (jtms/dependents tms (:consequence j)))))

(defn- drop-unowned-guard-justifications!
  "Drop each justification under `guard-informant` of a defeat of `f` that no rule firing
  or edge reading of `f` owns (`exc/guard-owners`): the defeat of a firing a replacing route took away
  (`special/drop-replaced-routes!`).  A
  change posts F's re-check (`special/recheck-defeat-target`)."
  [kb f]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        firings (into [] (comp (keep #(jtms/justification tms %))
                               (filter #(or (special/firing-informant? kb (:informant %))
                                            (= exc/edge-reading-informant (:informant %)))))
                      (jtms/supports tms f))
        gone  (into [] (comp (mapcat #(jtms/supports tms %))
                             (keep #(jtms/justification tms %))
                             (filter #(= guard-informant (:informant %)))
                             (remove #(seq (exc/guard-owners recs % firings)))
                             (map :id))
                    (reads/as-stored-naming (:index kb) sx/defeat-functor f))]
    (when (seq gone)
      (drop-justifications! kb gone)
      (special/recheck-defeat-target
       kb {:sentence (list sx/defeat-functor (sx/sentex-handle f))}))))

(defn place-guard-defeats!
  "For each `[j live? conds]` of `firings`, `j` a firing's or an edge reading's justification
  record and `conds` its block conditions or nil: store `(defeat (sentexHandle F))`, F its
  conclusion, at each context `guard-defeat-placements` or `edge-reading-defeat-placements`
  names, justified under `guard-informant` at `:default`, and drop each guard justification
  the firing owns (`guard-justifications`) that the current state no longer gives.  A firing
  that is not `live?` keeps none.  A change posts F's re-check (`special/recheck-defeat-target`).
  Returns the conclusions whose guard defeats moved.  With `drop?` false (a settle that sweeps
  nothing, `core/preview`'s) no justification is dropped, so a suspended blocker takes its
  defeat OUT and the rollback finds the records it left.  See docs/naf.md."
  ([kb firings] (place-guard-defeats! kb firings true))
  ([kb firings drop?]
   (let [recs (:records kb)
         place!
         (fn [[j live? conds]]
           (when (p/get-sentex recs (:consequence j))
             (let [s     (list sx/defeat-functor (sx/sentex-handle (:consequence j)))
                   want  (into #{} (map (fn [[q antes]] [s q antes]))
                               (when live?
                                 (-> (guard-defeat-placements kb j conds)
                                     (into (inheritance-defeat-placements kb j))
                                     (into (edge-reading-defeat-placements kb j)))))
                   have  (guard-justifications kb j)
                   gone  (if drop?
                           (into [] (keep (fn [[jid k]] (when-not (contains? want k) jid))) have)
                           [])
                   added (nm/sort-by-content-key (fn [[s q]] [s q]) (remove (set (vals have)) want))]
               (when (seq gone)
                 (drop-justifications! kb gone))
               (doseq [[s q antes] added] (justify-placed! kb s q antes guard-informant (:bindings j)))
               (when (or (seq gone) (seq added))
                 (special/recheck-defeat-target kb {:sentence s})
                 (:consequence j)))))]
     (into [] (keep place!) firings))))

;; ---- a firing places its conclusion -------------------------------------

(defn- mint-rule
  "Store the rule a generator firing generated (docs/generators.md), justified by the
  firing, and return its handle in the newly-created vector `place-conclusion` returns.  The
  mint is derived, so the ordinary relabel un-believes it when its licence goes
  (`res/rule-believed?`).  The checks are the assert entry point's (`checks/rule-violation`
  through `checks/check-rule!`, `special/index-rule-sentex`).  Returned as a new handle so
  `process-datum` joins a forward-capable rule over the stored facts, so a generator's two
  arrival orders agree with no retroactive sweep.  A refused mint is
  dropped and recorded, never thrown; a mint the `:arg-variable` arm convicts is stored and
  held inert (`checks/hold-rule-conviction!`)."
  [kb rule sentence pctx all-antes depth bindings strength subs]
  (let [sentence (directed-generated-rule sentence)
        ;; A generated rule is polycanonicalized as an asserted one is (`rules/expand-rule`),
        ;; and checked before any alternative is stored, since a mapv is not a transaction
        minted (rules/expand-rule sentence)]
    (if-let [v (some #(checks/rule-violation kb % pctx) minted)]
      (do (violations/report kb [(assoc v :sentence sentence :context pctx
                                        :rule (:rule-handle rule))])
          [])
      (into []
            (mapcat
             (fn [one]
               (let [[h s new?] (kb/find-or-create-sentex kb one pctx)]
                 (when new? (special/index-rule-sentex kb h s))
                 (jtms/ensure-node (reasoning/tms kb) h depth)
                 (when new? (checks/hold-rule-conviction! kb s))
                 (when-not (jtms/has-justification? (reasoning/tms kb) (:name rule) all-antes h
                                                    (jtms/justification-key (:name rule) all-antes subs))
                   (let [jid  (p/next-id (:records kb))
                         ;; content order is bought here, inside the dedup guard, for
                         ;; `place-fact-conclusion`'s reason: the question above is
                         ;; set-keyed and only the record being written needs an order
                         just (jtms/->just jid (:name rule) (kb/antecedent-order kb all-antes)
                                           h bindings strength subs)]
                     (p/put-justification (:records kb) just)
                     (jtms/add-justification (reasoning/tms kb) just)
                     ;; a `:default` blocker at the placement, or a guard below it,
                     ;; places a defeat of the minted rule
                     (when (and (integer? (:name rule)) (:watched? rule))
                       (place-guard-defeats! kb [[just true (guard-conditions-of rule)]]))))
                 (if new? [h] []))))
            minted))))

;; ---- the class a metatype route binds --------------------------------------------
;; A `:monotonic` membership `(T P)` whose type reaches an exact-arity class `C` through
;; `genl` edges IN at `:monotonic` binds P's length as `(C P)` does (docs/taxonomy.md,
;; "Arity").  The engine stores `(C P)` in CxUniverse, justified by the membership and one
;; path's edges (`arity/class-paths`), and keeps the justifications in step here.  No KB
;; rule states it: the rule would need a variable functor and an antecedent's class read.

(def arity-class-informant
  "The informant of a justification of a class membership `(C P)` a metatype route
  derives (`sync-arity-classes!`)."
  'arityClass)

(defn- arity-class-justifications
  "`{[sentence antecedents] jid}`: the justifications under `arity-class-informant` the
  stored membership `m` grounds, each keyed by its conclusion's sentence and its
  antecedents as a set."
  [kb m]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (into {} (keep (fn [jid]
                     (let [j (jtms/justification tms jid)]
                       (when (= arity-class-informant (:informant j))
                         (when-let [c (p/get-sentex recs (:consequence j))]
                           [[(:sentence c) (set (:antecedents j))] jid])))))
          (jtms/dependents tms m))))

(defn- place-arity-class!
  "Store the class membership `sentence` in CxUniverse, justified under
  `arity-class-informant` by `antes` at `:monotonic`, as `{:new [handle …] :violations
  [v]}`: the new class membership and the types its argument constraints mint, or the
  violation that leaves it unstored (`checks/constraint-admission`).  A membership an
  argument conviction convicts is stored and held, as `place-fact-conclusion` holds one."
  [kb sentence antes]
  (let [tms      (reasoning/tms kb)
        recs     (:records kb)
        ctx      sx/root-context
        existing (kb/find-sentex-handle kb sentence ctx)
        adm      (when-not existing (checks/constraint-admission kb sentence ctx))]
    (if-let [v (:violation adm)]
      {:new [] :violations [(assoc v :sentence sentence :context ctx)]}
      (let [[h s new?] (if existing
                         [existing (p/get-sentex recs existing) false]
                         (let [[h s] (kb/create-sentex kb sentence ctx)] [h s true]))]
        (when new?
          (when (:conviction adm) (checks/hold-argument-conviction! kb h (nm/functor sentence)))
          (checks/force-sentex! kb s)
          (special/derived-sentex-added kb s h))
        (jtms/ensure-node tms h (inc (long (reduce (fn [d a] (max (long d) (long (jtms/depth tms a))))
                                                   0 antes))))
        (when-not (jtms/has-justification? tms arity-class-informant antes h)
          (let [just (jtms/->just (p/next-id recs) arity-class-informant
                                  (kb/antecedent-order kb antes) h {} :monotonic)]
            (p/put-justification recs just)
            (jtms/add-justification tms just)))
        (let [args (when new? (special/deduce-arg-types kb (:entailments adm) h ctx))]
          {:new        (cond-> (into [] (special/minted-seeds kb (:new args))) new? (conj h))
           :violations (vec (:violations args))})))))

(defn sync-arity-classes!
  "Bring the class memberships the stored memberships `hs` derive in step with the `genl`
  edges as they stand, as `{:new [handle …] :violations [v]}`.  A `:monotonic` membership
  `(T x)` derives `(C x)` for each class `arity/class-paths` gives over the edges IN at
  `:monotonic`, justified by the membership and that path's edges (`place-arity-class!`).  A
  justification under `arity-class-informant` that the edges no longer give is dropped.  With
  `defer?` nothing is dropped and a membership owing a drop is queued (`arity/note-class!`)."
  ([kb hs] (sync-arity-classes! kb hs false))
  ([kb hs defer?]
   (let [tms  (reasoning/tms kb)
         recs (:records kb)
         ok?  #(arity/class-route-ok? tms %)
         ms   (->> (set hs)
                   (keep #(p/get-sentex recs %))
                   (nm/sort-by-content-key (fn [m] [(:sentence m) (:context m)])))]
     (special/with-recheck-reads
       (reduce
        (fn [acc m]
          (let [h     (:id m)
                [t x] (arity/membership-of m)
                want  (if (and t (= :monotonic (jtms/defeat-class tms h)))
                        (into {} (map (fn [[c path]] [[(list c x) (into #{h} path)] path]))
                              (arity/class-paths kb t ok?))
                        {})
                have  (arity-class-justifications kb h)
                gone  (into [] (keep (fn [[k jid]] (when-not (contains? want k) jid))) have)]
            (when (seq gone)
              (if defer?
                (arity/note-class! kb m true)
                (drop-justifications! kb gone)))
            (reduce (fn [acc [s antes]] (merge-with into acc (place-arity-class! kb s (vec antes))))
                    acc
                    (nm/sort-by-content-key first (remove #(contains? have %) (keys want))))))
        {:new [] :violations []}
        ms)))))

(defn- class-route-memberships
  "The stored memberships whose class memberships the stored fact `sentence` moves: a
  membership `(T x)` of a type reaching an exact-arity class (`arity/reaches-class?`),
  itself; and a class membership `(C x)`, the memberships of `x` in a type reaching one,
  whose class memberships a relabel of `(C x)` can have moved.  A relabel of `(T x)`
  moves itself too: the sync reads its defeat class (`sync-arity-classes!`).  A `genl`
  edge moves them through the taxonomy (`arity-class-ends-moved!`)."
  [kb sentence h]
  (when (and (seq? sentence) (symbol? (first sentence)))
    (let [[f a]  sentence
          recs   (:records kb)
          idx    (:index kb)
          route? (fn [t] (and (symbol? t) (not (contains? arity/exact-classes t))
                              (arity/reaches-class? kb t)))
          of-x   (fn [x] (into [] (filter #(let [[t x'] (arity/membership-of (p/get-sentex recs %))]
                                             (and (= x x') (route? t))))
                               (reads/as-stored-unary-with-arg-global idx x)))]
      (cond
        (and (= 2 (count sentence)) (symbol? a) (contains? arity/exact-classes f)) (of-x a)
        (and (= 2 (count sentence)) (symbol? a) (route? f))                         [h]))))

(defn arity-class-ends-moved!
  "Sync the class memberships of the stored memberships of every type at or below one of
  `ends`, the lower ends of moved `genl` edges (`arity/take-class-ends!`), that reaches an
  exact-arity class (`sync-arity-classes!`), over the unscoped closure: the class
  membership is stored in CxUniverse and reads the edges in every context, as a
  relation's length does.  Answers `{:new :violations}`.  `defer?` is
  `sync-arity-classes!`'s."
  ([kb ends] (arity-class-ends-moved! kb ends false))
  ([kb ends defer?]
   (let [tax  (reasoning/taxonomy kb)
         idx  (:index kb)
         recs (:records kb)
         ts   (into #{} (comp (filter #(and (symbol? %) (arity/reaches-class? kb %)))
                              (mapcat #(conj (set (tax/specs-global tax %)) %)))
                    ends)
         ms   (into #{} (comp (mapcat #(reads/as-stored-with-functor idx %))
                              (filter #(some? (arity/membership-of (p/get-sentex recs %)))))
                    ts)]
     (if (seq ms) (sync-arity-classes! kb ms defer?) {:new [] :violations []}))))

(defn arity-classes-moved!
  "Sync the class memberships the stored records `sxs` move (`class-route-memberships`,
  `sync-arity-classes!`): a membership arriving, its class rising, or a relabel of a class
  membership or of a sentence installing `genl` edges (`relabel?`), which syncs below the
  edges' lower ends (`tax/installed-edges`, `arity-class-ends-moved!`): a strength change
  moves no edge in the taxonomy.  Answers `{:new :violations}`.  `defer?` is
  `sync-arity-classes!`'s: a write's store path and its run pass `*rollback-scope*`."
  ([kb sxs relabel?] (arity-classes-moved! kb sxs relabel? false))
  ([kb sxs relabel? defer?]
   (when-not relabel? (arity/classes-synced! kb (keep :id sxs)))
   (let [facts (filter #(and % (nil? (:antecedent %))) sxs)
         ms    (into #{} (mapcat #(class-route-memberships kb (:sentence %) (:id %))) facts)
         ends  (when relabel? (into #{} (comp (mapcat #(tax/installed-edges (:sentence %))) (map first))
                                    facts))]
     (merge-with into
                 (if (seq ms) (sync-arity-classes! kb ms defer?) {:new [] :violations []})
                 (if (seq ends) (arity-class-ends-moved! kb ends defer?) {:new [] :violations []})))))

(defn- place-fact-conclusion
  "Persist/justify a rule conclusion `conseq`, written `written` before the reify (or nil),
  in context `pctx` at justification `strength` (:monotonic / :default); return the handles
  newly created: the conclusion, plus a copy in each context its predicate is declared to
  lift into.  The definitional constraints and stratification are checked on the derivation
  path (`checks/constraint-admission`).  A clash with a second believed sentex is placed and
  weighed by `settle`.  A violation with no second side is dropped and reported to
  `core/violations`, never thrown.  An argument conviction `assert` holds inert is stored and
  held in the `:out` forced set (`checks/hold-argument-conviction!`).  See docs/nmtms.md."
  [kb rule conseq pctx all-antes depth bindings strength subs written]
  (let [existing (kb/find-sentex-handle kb conseq pctx)
        ;; The checks run only when the conclusion is new: a re-derivation adds a justification,
        ;; not content, and `args-problem` walks a type's spec closure per subtype (paying it per
        ;; firing made the starter's load ten times slower).  A derived `genl` edge can close a
        ;; cycle through negation, so the rule-set constraint runs too; violations are dropped and
        ;; reported.  One pass over the definitional checks answers both the violation and what the
        ;; argument constraints entail, materialized once the conclusion has a handle.
        adm      (when-not existing (checks/constraint-admission kb conseq pctx))
        v        (when-not existing (fact-violation kb rule conseq pctx adm))
        ;; ...and the forced-monotonic check, which a stored conclusion owes as well: a
        ;; firing it convicts is stored and held void, so it supports nothing while the
        ;; forced-monotonic set rules it out and supports its conclusion once the set stops
        forced   (when-not v (checks/forced-conclusion-violation kb (:rule-handle rule) conseq))
        ;; logged when void at some reader, held void in the network when void at every
        ;; one (`checks/network-void?`)
        void?    (and forced (checks/network-void? kb (:rule-handle rule) conseq))]
    (if v
      (drop-fact-conclusion! kb rule conseq pctx v)
      (let [[h s new?] (if existing
                         [existing (p/get-sentex (:records kb) existing) false]
                         (let [[h s] (kb/create-sentex kb conseq pctx)] [h s true]))
            ;; the dedup key, built once for the question and the add that follows it
            jkey       (jtms/justification-key (:name rule) all-antes subs)
            added?     (volatile! false)]
        ;; a new conclusion takes its forced memberships before anything can label it
        (when new?
          (when (:conviction adm) (checks/hold-argument-conviction! kb h (nm/functor (:sentence s))))
          (checks/force-sentex! kb s))
        ;; the derivation-path choke point: a derived genl edge reaches the closure,
        ;; and a derived fact is a re-check trigger like an asserted one
        (when new? (special/derived-sentex-added kb s h))
        ;; ...and a derived use or value of a minted constant queues its copies, as an
        ;; asserted one does; a correspondence derivation queues nothing
        (when (and new? (not= res/correspondence-predicate (:name rule)))
          (nat-read/note-values kb [(:sentence s)] true))
        (jtms/ensure-node (reasoning/tms kb) h depth)
        (when (vreset! added? (not (jtms/has-justification? (reasoning/tms kb) (:name rule) all-antes h jkey)))
          (let [jid  (p/next-id (:records kb))
                ;; The content sort is paid here: `all-antes` arrives in join order and the record must
                ;; not inherit it (`kb/antecedent-order`).  The dedup above is keyed on the antecedents as a
                ;; set (`jtms/just-key`), so it is order-free; sorting before it would print a sentence per
                ;; antecedent per firing where the record is written once per justification.  The rule's
                ;; own handle is sorted out, since `->just` drops the informant from the stored vector.
                inf  (:name rule)
                just (jtms/->just jid inf (kb/antecedent-order kb (remove #(= inf %) all-antes))
                                  h bindings strength subs)]
            (when void? (jtms/set-forced (reasoning/tms kb) :void [jid] true))
            ;; a convicted firing is logged once, as its justification is added;
            ;; `core/violations` reads its entry off the stored firing
            (when forced
              (violations/log-entries kb [(assoc forced :sentence (:sentence s) :context pctx
                                                 :rule (:rule-handle rule))]))
            (p/put-justification (:records kb) just)
            (jtms/add-justification (reasoning/tms kb) just jkey)
            ;; a guard that holds below the placement, or a `:default` blocker at it,
            ;; places a defeat of the firing
            (when (and (integer? inf) (or (:watched? rule) (:inherited? rule)))
              (place-guard-defeats! kb [[just true (guard-conditions-of rule)]]))
            ;; a firing over a route the witness rule now names replaces the same firing
            ;; over the route it named before, which only a stored conclusion can hold
            (when-not new?
              (when-let [r (special/drop-replaced-routes! kb just)]
                (integrate/apply-removals! kb r)
                (drop-unowned-guard-justifications! kb h)))
            ;; a conclusion a permuting mark re-spelled, or naming a sorted constant, keeps
            ;; the spelling it was drawn in, for the mark's leaving to put it back at
            (let [w (if (and written (not= written conseq) (nat/permutes-reified? kb written))
                      written
                      conseq)]
              (when (and (not= w (:sentence s)) (integer? (:name rule))
                         (or (not= w conseq) (integrate/permuting-sentence? kb conseq)))
                (integrate/note-derived-spelling! kb h jid w)))))
        ;; Everything a conclusion means beyond itself, in the order `assert-entry/assert-one`
        ;; runs it: the three merges, the decontextualized copy and the argument entailments
        (let [;; A rule concluding one of the three equality relations merges exactly as
              ;; an asserted one does: the closure learns the edge, migration restates the sentexes it
              ;; displaces, and `recover` agrees with the running KB.  Reached by name because
              ;; `integrate-transitive` discards what an arm returns and the twins and violations are
              ;; the work.  After the justification above, since migration takes only the equalities it
              ;; believes.
              eq   (when (and new? (kb/equality-sentence? conseq))
                     (special/integrate-equality-sentex kb s h))
              ;; a derived second value for a functional predicate merges as an asserted one does, since
              ;; `functional-problem` derives an equality and does not refuse a symbol clash
              fnl  (when new? (special/derive-functional-equalities kb conseq pctx h))
              ;; ...and a derived `(functional P)` reaches P's stored facts as an asserted one does.  A
              ;; declaration held OUT derives no equality; the settle that brings it IN runs the sweep
              ;; (`special/revived-declaration-sweeps`)
              in   (and new? (jtms/in? (reasoning/tms kb) h))
              fex  (when in (special/equate-existing kb conseq))
              ;; ...and the edge's side of it: a derived `genl` edge between predicates
              ;; brings stored sub-predicate facts under a `functional` mark above them,
              ;; as an asserted one does
              fed  (when new? (special/equate-under-edge kb conseq))
              ;; ...and the antisymmetric merge, in the same three arrival orders a rule
              ;; can reach it by — a derived converse, a derived declaration, a derived edge
              asym (when new? (special/derive-antisymmetric-equalities kb conseq pctx h))
              axe  (when in (special/antisym-equate-existing kb conseq))
              axd  (when new? (special/antisym-equate-under-edge kb conseq))
              ;; ...and a derived tuple mark or edge offers the stored tuples to the
              ;; candidates the settle places, as an asserted one does
              _    (when new? (special/offer-marked-existing kb conseq))
              _    (when new? (special/offer-marked-under-edge kb conseq))
              ;; ...and a derived `(symmetric P)` re-spells the rows stored before it, as an asserted one does
              symx (when new? (integrate/commute-existing kb conseq h))
              ;; nil when nothing merged, which is nearly every conclusion; a fixpoint re-derives the
              ;; same conclusion every round, so this arm must add no work
              mig  (when (or eq fnl fex fed asym axe axd symx)
                     (merge-with into {:new [] :superseded [] :violations []}
                                 eq fnl fex fed asym axe axd symx))
              ;; The spellings those merges retired are applied here and not left to the settle
              ;; (`special/supersession-map`), so the twins below are seeds: the retired spelling stops
              ;; matching at once, and the restatement must be on the agenda.
              _    (when (seq (:superseded mig))
                     (special/refresh-supersessions kb (:superseded mig)))
              ;; A decontextualized predicate is a claim about the predicate, so the lift runs on
              ;; concluded content as on asserted (`assert-one`).  It runs for a re-derivation too, since
              ;; a conclusion stored before the declaration picks up its copy then; the copy is enqueued
              ;; like the conclusion.
              lift (special/deduce-lifts kb conseq h pctx)
              ;; The argument constraints entail of a derived conclusion what they entail of an
              ;; asserted one, drawn only for a new conclusion
              args (merge-with into
                               (special/deduce-arg-types kb (:entailments adm) h pctx)
                               (when new? (special/deduce-below kb conseq h pctx)))
              ;; ...and a conclusion that *is* a declaration reaches back over the stored
              ;; facts, as an asserted one does.
              back (special/entail-existing kb conseq h)
              ;; ...and a derived `genl` edge between predicates brings stored
              ;; sub-predicate facts under the declarations above them, as an asserted
              ;; one does
              down (special/entail-under-edge kb conseq)
              ;; ...and the class membership a metatype route derives from a derived
              ;; membership or edge, as from an asserted one
              cls  (when new? (arity-classes-moved! kb [s] false *rollback-scope*))]
          (when (or (seq (:violations mig)) (seq (:violations lift)) (seq (:violations args))
                    (seq (:violations back)) (seq (:violations down)) (seq (:violations cls)))
            (violations/report kb (concat (:violations mig) (:violations lift)
                                          (:violations args) (:violations back)
                                          (:violations down) (:violations cls))))
          ;; The arms above install the conclusion in its cache unconditionally; a void firing leaves
          ;; the node OUT from creation, so no settle region names it, and its caches are reconciled
          ;; here as `recover` does
          (when (and void? new?) (special/reconcile-belief-change kb [h]))
          (-> (if new? [h] [])
              (into-some (special/minted-seeds kb (:new mig)))
              (into-some (:new lift))
              (into-some (special/minted-seeds kb (:new args)))
              (into-some (special/minted-seeds kb (:new back)))
              (into-some (special/minted-seeds kb (:new down)))
              (into-some (:new cls))
              ;; a derived genl edge seeds the facts below it as an asserted one does, but
              ;; only when the firing added a justification: the seeds include the firing's
              ;; own trigger, and a re-derivation re-seeding it never drains the agenda
              (into-some (when @added? (special/subsumption-seeds kb conseq)))
              ;; and a derived link of a transitive predicate extends its answered closure as an
              ;; asserted one does.  Only for a new conclusion: this seeds the partner triggers of the
              ;; rules joined to the predicate, which include the rule that concluded the link, so a
              ;; re-derivation would re-seed its own trigger and the agenda (a plain queue with no
              ;; dedup) would never drain (`max-derivations`).
              (into-some (when new? (special/transitive-seeds kb conseq)))))))))

(defn- mint-violation
  "The refusal a nested mint threw, `e`, as the `:mint-refused` violation that drops the
  conclusion it was minting for.  One kind rather than the thrown one: the mint is a whole
  assert, and what it refused is one of the sentences the mint writes about the constant,
  not the conclusion, so `:refusal` carries the thrown kind and `:message` says which
  sentence."
  [^clojure.lang.ExceptionInfo e]
  {:violation :mint-refused
   :detail    {:refusal (get (ex-data e) :type) :message (ex-message e)}})

(defn- reify-conclusion
  "`[sentence violation]` for the conclusion `conseq` a firing places: `conseq` with every
  ground reifiable NAT replaced by its term and nil, or the conclusion as far as it could
  be reified and the violation that drops it (docs/nat.md, Derivation path).
  `violation-of` is the placement's check list, asked under `checks/*entry-mints?*` before
  any mint, so a dropped conclusion mints nothing.  A refused mint is the `:mint-refused`
  violation.  The mints run under `*defer-settle?*`.  One walk that allocates nothing for
  a conclusion naming no reifiable NAT."
  [kb conseq pctx violation-of]
  (nat/queue-split-uses! kb conseq)
  (if-not (nat/names-reifiable-nat? kb conseq)
    [conseq nil]
    (let [known (nat-read/reify-existing kb conseq pctx)]
      (if-not (nat/names-reifiable-nat? kb known)
        [known nil]
        (if-let [v (binding [checks/*entry-mints?* true] (violation-of known))]
          [known v]
          (try
            [(binding [wiring/*defer-settle?* true] (nat/maybe-reify-nats kb known pctx)) nil]
            (catch clojure.lang.ExceptionInfo e
              (if (get (ex-data e) :type)
                [known (mint-violation e)]
                (throw e)))))))))

(defn- place-conclusion
  "Place one firing's conclusion: a rule is a generator's mint (`mint-rule`), everything
  else a fact (`place-fact-conclusion`).  The split is here so a fresh firing and a released
  refusal make it alike.  Every ground reifiable NAT in the conclusion is reified first
  (`reify-conclusion`).  `all-antes` is the antecedent handles in any order; both arms sort
  it by content (`kb/antecedent-order`) when writing a justification, and `bindings` lose the
  join's `?ctx`, which a full join binds and a trigger's does not.  `subs` is the firing's
  subsumptions or nil."
  [kb rule conseq pctx all-antes depth bindings strength subs]
  (let [bindings (dissoc bindings '?ctx)
        rule?  (rules/rule-sentence? (peek (sx/peel-rule-wrapper conseq)))
        [c v]  (reify-conclusion kb conseq pctx
                                 (if rule?
                                   #(generated-rule-violation kb % pctx)
                                   #(fact-violation kb rule % pctx (checks/constraint-admission kb % pctx))))]
    (cond
      (and v rule?) (do (violations/report kb [(assoc v :sentence (directed-generated-rule c) :context pctx
                                                      :rule (:rule-handle rule))])
                        [])
      v             (drop-fact-conclusion! kb rule c pctx v)
      rule?         (mint-rule kb rule c pctx all-antes depth bindings strength subs)
      :else         (place-fact-conclusion kb rule c pctx all-antes depth bindings strength subs conseq))))

(defn- placement-ingredients
  "Where a firing's conclusion may live, and which taxonomy supporters it names getting
  there: `[placement-contexts {placement-context [edge-handle]}]`, the handle list holding
  both the `genl` edges the match subsumed through and the `genlCx` edges the placement sees
  its ingredients over.  The placement is the maximal contexts that see the rule, the
  antecedent facts and the edges' supporters, chosen to constrain the placement least:
  where a maximal context seeing the rule and facts also sees a path, the edges add no
  constraint.  Only where a candidate sees no path does the conclusion descend
  (`descent-placements`) and not land in `:no-placement`.  A supporter with no recorded
  context drops out."
  [kb rule links fact-handles fact-ctxs strict]
  (placements-over kb links (cons (:rule-handle rule) fact-handles) (cons (:context rule) fact-ctxs)
                   nil strict))

;; ---- the families that place their nogoods -----------------------------

(defn- route-placements
  "The `[context antecedents]` placements of the nogood over `members` that the `routes`
  give (`membership/routes`, `related/routes`, `tuple/routes`): for each route and each
  choice of one believed supporter per key it reads, or each of its `:choices`, each context
  `placements-over` places the members, supporters and subsumptions at, with them and the
  edge handles as antecedents.  A placement that reads a `siblingDisjointException` exempting
  the route's pair, or one of its `:pairs`, is left out (`tax/route-exempted?`), as is one
  `:excluded-at` names.  A separation-denial route holds the soundness rule of
  `res/separation-denials`: each `:strict-links` reaches at `:monotonic` (`tax/reach-support`)
  and each `:strict-keys` supporter holds there (`res/holding-class`).  With `within`, only the
  placements in it."
  [kb members routes within]
  (let [tax   (reasoning/taxonomy kb)
        recs  (:records kb)
        exc?  (tax/sib-exceptions? tax)
        cls   (delay (res/holding-class kb))
        mctxs (mapv #(:context (p/get-sentex recs %)) members)]
    (into #{}
          (for [{:keys [keys links choices excluded-at strict-links strict-keys pairs] :as route} routes
                ;; a supporter of a strict key is kept only at `:monotonic`, read key by key
                ;; before the product; `membership/routes` alone gives `:strict-keys`, and
                ;; no `:choices`
                sups (or choices
                         (route-supporters kb keys
                                           (when (seq strict-keys)
                                             (fn [k [h]] (or (not (contains? strict-keys k))
                                                             (= :monotonic (@cls h)))))))
                :let [[ps m] (placements-over kb links (into (vec members) (map first) sups)
                                              (into mctxs (map second) sups) within
                                              (when (seq strict-links) (set strict-links)))]
                pctx ps
                :when (not (and exc? (tax/route-exempted? tax route pctx)))
                :when (not (and exc? (seq pairs)
                                (some #(tax/route-exempted? tax {:pair % :mark? true} pctx) pairs)))
                :when (every? (fn [[sub super]]
                                (tax/reach-support tax :genl sub super pctx @cls [:monotonic]))
                              strict-links)
                :when (not (and excluded-at (excluded-at pctx)))]
            [pctx (-> (set members) (into (map first) sups) (into (get m pctx)))]))))

(defn- content-key
  "The content order of a nogood's member set: each member's sentence and context, sorted."
  [kb ms]
  (sort nm/compare-form (map #(let [s (p/get-sentex (:records kb) %)] [(:sentence s) (:context s)]) ms)))

(defn- stale-sets
  "The member sets of the nogoods placed over a handle of `hs` that `kind-of` names and
  `current`, a set of member sets, does not hold.  Given the context set `within`, only
  the placements in it are read: the placed `(contradicts …)` stated there, while fewer
  are than the term index holds sentexes naming a handle of `hs`, otherwise that read
  filtered."
  [kb hs kind-of current within]
  (let [recs (:records kb)
        idx  (:index kb)
        hs   (set hs)
        ms   (cond
               (nil? within)
               (into [] (comp (mapcat #(placed-justifications kb %)) (map :members)) hs)

               (< (reads/stored-count-with-functor-in idx 'contradicts within)
                  (transduce (map #(count (reads/as-stored-naming-handle idx %))) + hs))
               (filter #(some hs %)
                       (placed-members kb (reads/as-stored-with-functor-in idx 'contradicts within)))

               :else
               (into [] (comp (mapcat #(placed-justifications kb %))
                              (filter #(contains? within (second (:key %))))
                              (map :members))
                     hs))]
    (into #{} (comp (remove current) (filter #(kind-of recs %))) ms)))

(def ^:private plan-batch
  "The most nogoods of one call `plan-sets` reads the routes of before it writes their
  placements: past it, the rest are read and written a batch at a time, in the same
  content order, so the reads a pass holds are bounded by the batch and not by the
  family."
  4096)

(defn- plan-sets*
  [kb reach full reached nogoods-of kind-of routes-of owns? tick plan?]
  (let [tms     (reasoning/tms kb)
        under   (:under reach)
        full    (set full)
        reached (when under (into #{} (remove full) reached))
        fngs    (nogoods-of full)
        fms     (into #{} (map :members) fngs)
        ngs     (into fngs (when (seq reached) (remove #(fms (:members %)) (nogoods-of reached))))
        current (into #{} (map :members) ngs)
        fstale  (stale-sets kb (if plan? (into #{} (comp (filter plan?) (mapcat :members)) fngs) full)
                            kind-of current nil)
        stale   (into fstale (when (seq reached) (stale-sets kb reached kind-of current under)))
        within  (fn [ms] (when-not (or (fms ms) (fstale ms)) under))
        removes (mapv (fn [ms] [ms [] (within ms)])
                      (nm/sort-by-content-key #(content-key kb %) nm/compare-form stale))
        plan    (fn [ngs tick]
                  (into [] (comp (if tick (map (fn [ng] (tick) ng)) identity)
                                 (if plan? (filter plan?) identity)
                                 (filter (fn [ng] (every? #(jtms/network-in? tms %) (:members ng))))
                                 (map (fn [{ms :members :as ng}]
                                        (let [w (within ms)]
                                          ;; a declared member's verdicts read every placement
                                          [ms (route-placements kb ms (routes-of ng)
                                                                (when (and w (empty? (declared-members kb ms))) w))
                                           w]))))
                        ngs))
        write   (fn [planned] (into [] (mapcat (fn [[ms ps w]] (place-justified! kb ms ps (fn [core] (owns? ms core)) w)))
                                    planned))
        [ngs more] (split-at plan-batch (nm/sort-by-content-key #(content-key kb (:members %)) nm/compare-form ngs))
        places  (plan ngs tick)]
    ;; a placement's writes move no route, witness or member label another nogood of the
    ;; family reads, so a batch read after the batches before it were written reads what
    ;; it would have read before them, and the writes keep their content order
    (fn []
      (with-open [r (progress/start ::place-sets "settle: place the nogoods"
                                    (+ (count removes) (count places) (count more)))]
        (into (let [made (write (into removes places))]
                (progress/tick! r (+ (count removes) (count places)))
                made)
              (mapcat #(let [made (write (tax/with-neighbours (atom {}) (fn [] (plan % nil))))]
                         (progress/tick! r (count %))
                         made))
              (partition-all plan-batch more))))))

(defn- plan-sets
  "`place-sets!` with its reads taken now and its writes deferred: a fn of no arguments
  that places and removes what the reads decided and returns the handles created.  A family
  over many terms reads every term's routes before it places the first, sharing
  `*witnesses*` (docs/nmtms.md, \"The placement pass\").  Past `plan-batch` nogoods it reads
  and writes a batch at a time.  The reads hold the scoped walks' neighbours and the other
  reads a pass repeats (`tax/with-neighbours`, `tax/pass-held`).  `tick`, when given, is
  called once for each nogood of the first batch as its read begins.  A nogood `plan?`
  holds false of keeps its placements, and the stale sets are read over the others' members."
  ([kb reach full reached nogoods-of kind-of routes-of owns?]
   (plan-sets kb reach full reached nogoods-of kind-of routes-of owns? nil nil))
  ([kb reach full reached nogoods-of kind-of routes-of owns? tick plan?]
   (tax/with-neighbours (atom {}) #(plan-sets* kb reach full reached nogoods-of kind-of routes-of owns? tick plan?))))

(defn- place-sets!
  "Place each nogood `nogoods-of` gives for the handles `full` or `reached` whose members
  are all IN (`jtms/network-in?`) at the placements its `routes-of` gives, and remove the
  placements of each member set over one of those handles that it no longer gives
  (`stale-sets`), each under `owns?` (`place-justified!`), in content order.  `nogoods-of`
  takes a handle set.  A nogood found through `reached` alone compares only its placements in
  `reach`'s `:under` (`special/drain-context-moves!`).  Returns the handles created.  The reads
  all precede the writes (`plan-sets`)."
  [kb reach full reached nogoods-of kind-of routes-of owns?]
  ((plan-sets kb reach full reached nogoods-of kind-of routes-of owns?)))

(defn- genl-lower-ends
  "The lower end of each `genl` edge stated by a handle of `hs`."
  [kb hs]
  (let [recs (:records kb)]
    (with-open [r (progress/start ::genl-lower-ends "settle: read the genl edges' lower ends" nil)]
      (into #{} (keep (fn [h] (let [s (:sentence (p/get-sentex recs h))]
                                (when (and (seq? s) (= 'genl (first s)) (= 3 (count s))
                                           (symbol? (second s)))
                                  (second s)))))
            (cap/hinting (cap/prefetcher recs) cap/recovery-hint-chunk (progress/each r hs))))))

(defn- reach-grounds
  "The grounds stated where a `genlCx` move `reach` (`special/drain-context-moves!`'
  `:reach`) reaches, read once for the families of one pass: the handles stated in the
  contexts of `:below` that state a `genl` edge or a declaration
  (`tax/asserting-contexts-among`), read by functor (`tax/grounds-stated-in`), as
  `{:lower :keys}`, the lower ends of their `genl` edges (`genl-lower-ends`) and the
  flat-cache keys they support.  nil when no context of `:below` states one, or when
  `reach` is nil or the relation was rebuilt."
  [kb reach]
  (when (and reach (not (:all? reach)))
    (let [tax (reasoning/taxonomy kb)
          cs  (into [] (filter (tax/asserting-contexts-among tax (:below reach))) (:below reach))]
      (when (seq cs)
        (let [gs (tax/grounds-stated-in tax cs)]
          {:lower (genl-lower-ends kb gs) :keys (tax/supported-keys tax gs)})))))

(defn- grounds-of
  "`reach-grounds`' `{:lower :keys}` of the handles `hs`."
  [kb hs]
  {:lower (genl-lower-ends kb hs) :keys (tax/supported-keys (reasoning/taxonomy kb) hs)})

(defn- reach-handles
  "What a `genlCx` move `reach` (`special/drain-context-moves!`' `:reach`) can give or take a placement through,
  `[handles grounds]`: the candidates (`decide/handles-at`) stated in a context of its
  `:below`, and `grounds`, the delay of `reach-grounds` the pass holds, whose ends reach
  nogoods over the types below them (`ground-ends`).  nil when `reach` is, `::all` when
  the relation was rebuilt."
  [c reach grounds]
  (cond
    (nil? reach)  nil
    (:all? reach) ::all
    :else
    (let [bl (:below reach)]
      [(set (when (seq bl) (decide/handles-at c bl))) @grounds])))

(defn- ground-ends
  "The types the grounds `{:lower :keys}` (`reach-grounds`, `grounds-of`) reach a
  membership nogood under: the lower end of a stated `genl` edge, and the ends of a
  separation or cover declaration's flat-cache keys (`tax/separation-ends`)."
  [kb {:keys [lower keys]}]
  (let [tax (reasoning/taxonomy kb)]
    (into (into #{} (comp (keep #(tax/separation-ends tax %)) cat) keys) lower)))

(defn- mark-ends
  "The predicates the grounds `{:lower :keys}` (`reach-grounds`, `grounds-of`) reach a
  tuple nogood under: the lower end of a stated `genl` edge with a mark at or above it
  (`tuple/under-marks`), and the predicates a mark's flat-cache key names
  (`tuple/owned?`'s keys)."
  [kb {:keys [lower keys]}]
  (let [tax (reasoning/taxonomy kb)]
    (into (into #{} (mapcat (fn [[kind a b]] (case kind :prop [b] :functional-in-arg [a] :negates a nil))) keys)
          (tuple/under-marks tax lower))))

(def ^:private edge-reading-rule
  "The rule map `place-fact-conclusion` places an edge reading under: the engine informant
  and no rule handle."
  {:name exc/edge-reading-informant :rule-handle nil})

(defn- edge-readings-wanted
  "The edge readings the `:supertype` nogoods of term `x` under the candidate index `c`
  owe, each `[reading context antecedents member link]`: for a membership `(s x)` beside
  a denial of `(q x)`, the reading `(q x)` at each placement of the membership and a
  `genl` path from `s` to `q` (`placements-over`) that sees no path held at `:monotonic`
  (`subsumption-support` with the link `strict`)."
  [kb c x]
  (let [recs (:records kb)]
    (into []
          (comp (filter #(= :supertype (:kind %)))
                (mapcat (fn [{:keys [members]}]
                          (let [sxs (keep #(p/get-sentex recs %) members)
                                m   (first (remove #(sx/negation? (:sentence %)) sxs))
                                d   (first (filter #(sx/negation? (:sentence %)) sxs))]
                            (when (and m d)
                              (let [link    [(first (:sentence m)) (first (second (:sentence d)))]
                                    reading (list (second link) x)]
                                (when-let [[ps support] (placements-over kb [link] [(:id m)] [(:context m)])]
                                  (binding [tax/*network-belief* true]
                                    (into []
                                          (comp (remove #(subsumption-support kb [link] % #{link}))
                                                (map (fn [pc] [reading pc (into [(:id m)] (get support pc))
                                                               (:id m) link])))
                                          ps))))))))
                (distinct))
          (membership/nogoods-of c x))))

(defn- fed-firings
  "The ids of the firing justifications resting on the membership `h` that climbed the
  subsumption `link`."
  [kb h link]
  (let [tms (reasoning/tms kb)]
    (into [] (filter (fn [jid]
                       (let [j (jtms/justification tms jid)]
                         (and (special/firing-informant? kb (:informant j))
                              (some #(= link (subvec (vec %) 0 2)) (:subsumptions j))))))
          (jtms/dependents tms h))))

(defn- sync-edge-readings!
  "Bring the edge readings resting on the memberships of the terms `xs` (`hs-of`) to what
  their `:supertype` nogoods under the candidate index `c` owe (`edge-readings-wanted`):
  place each wanted one as a firing is (`place-fact-conclusion`) with its guard defeats,
  and drop each other `exc/edge-reading-informant` justification.  A membership a reading
  arrives at or leaves loses the firings it fed through the link (`fed-firings`), and is
  re-chained.  Returns `[made seeds]`: the handles created and the memberships to
  re-chain.  Reads the dependents of the members of a term's `:supertype` nogoods and of
  those `sup` names (`membership/take-moved!`), the only handles a reading rests on."
  [kb c xs sup]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        made  (volatile! [])
        seeds (volatile! #{})
        reseed! (fn [h link]
                  (let [fs (fed-firings kb h link)]
                    (when (seq fs) (drop-justifications! kb fs))
                    (vswap! seeds conj h)))]
    (doseq [x xs
            :let [hs (into (set (get sup x)) (comp (filter #(= :supertype (:kind %))) (mapcat :members))
                           (membership/nogoods-of c x))]
            :when (seq hs)]
      (let [want  (edge-readings-wanted kb c x)
            keyed (into #{} (map (fn [[r pc antes]] [r pc (set antes)])) want)
            have  (into [] (comp (mapcat (fn [h] (map #(vector h %) (jtms/dependents tms h))))
                                 (distinct)
                                 (filter #(= exc/edge-reading-informant
                                             (:informant (jtms/justification tms (second %))))))
                        (sort hs))
            stale (into [] (remove (fn [[_ jid]]
                                     (let [j (jtms/justification tms jid)
                                           r (p/get-sentex recs (:consequence j))]
                                       (contains? keyed [(:sentence r) (:context r) (set (:antecedents j))]))))
                        have)]
        (doseq [[h jid] stale :when (jtms/justification tms jid)]
          (let [r (p/get-sentex recs (:consequence (jtms/justification tms jid)))]
            (drop-justifications! kb [jid])
            (reseed! h [(first (:sentence (p/get-sentex recs h))) (first (:sentence r))])))
        (doseq [[reading pc antes h link] want]
          (let [rh (kb/find-sentex-handle kb reading pc)]
            (when-not (and rh (jtms/has-justification? tms exc/edge-reading-informant antes rh))
              (vswap! made into (place-fact-conclusion kb edge-reading-rule reading pc antes
                                                       (inc (reduce max 0 (map #(jtms/depth tms %) antes)))
                                                       {} :monotonic nil nil))
              (reseed! h link))
            (when-let [rh (kb/find-sentex-handle kb reading pc)]
              (when-let [j (some (fn [jid] (let [j (jtms/justification tms jid)]
                                             (when (and (= exc/edge-reading-informant (:informant j))
                                                        (= (set antes) (set (:antecedents j))))
                                               j)))
                                 (jtms/supports tms rh))]
                (place-guard-defeats! kb [[j true nil]])))))))
    [@made (vec (sort @seeds))]))

(defn- edge-read-links
  "The set of the positive links of `links` whose matched membership an edge reading of
  the link's super rests on (`exc/edge-read-functors`), or nil: the reading answers for
  the term where no path from the sub to the super is held at `:monotonic`, so
  `derive-conclusion` places the firing through the link only where one is, and reports no
  missing placement for it.  One count read while no body is stored in both polarities."
  [kb matched record-of links]
  (when (and (seq links) (reads/stores-opposed? (:index kb)))
    (not-empty
     (into #{} (keep (fn [[ak h link]]
                       (when (and (symbol? ak) (nil? link))
                         (when-let [s (:sentence (record-of h))]
                           (let [fk (rules/antecedent-key s)]
                             (when (and (symbol? fk) (not= ak fk)
                                        (contains? (exc/edge-read-functors kb h) ak))
                               [fk ak]))))))
           matched))))

(defn- place-memberships!
  "Place the membership nogoods whose placement can have moved, remove the placements of those gone,
  and return the handles created: the nogoods of the terms `moved`'s `:terms` names (`membership/take-moved!`),
  of the terms with a membership or denial among the handles `fresh` the pass relabelled or `placed`
  (`placed-members`), of the terms under a separation or cover declaration
  (`membership/terms-under`) or a `genl` edge (`membership/terms-under-edges`) among `fresh` or
  `edge-moved` names (`membership/take-edge-moved!`), and of the terms with a candidate a `genlCx`
  move reaches (`reach-handles`, `ground-ends`).  A term an edge alone names places only the nogoods
  `membership/reaches-lows?` holds of (docs/nmtms.md).  Each is placed at its routes' placements
  (`membership/routes`, `route-placements`).  `minted` takes `sync-edge-readings!`'s seeds."
  [kb c {moved :terms sup :supertype} edge-moved reach grounds fresh placed minted]
  (when (or (seq moved) (seq (membership/nogoods-terms c)))
    (let [tax   (reasoning/taxonomy kb)
          recs  (:records kb)
          w     (decide/unscoped-closures tax)
          rh    (reach-handles c reach grounds)
          flows (genl-lower-ends kb fresh)
          other (-> (set (keys moved))
                    (into (membership/terms-of kb c fresh))
                    (into (membership/terms-of kb c placed))
                    (into (membership/terms-under kb w c (into #{} (comp (keep #(tax/separation-ends tax %)) cat)
                                                               (tax/supported-keys tax fresh))))
                    (into (when (= ::all rh) (membership/nogoods-terms c))))
          ;; a relabelled `genl` edge can move its defeat class, which a cover refuted
          ;; through a separation's denial reads at the placement
          edged (into (set (:terms edge-moved)) (membership/terms-under-edges kb w c flows))
          full  (into other edged)
          moves (when (vector? rh)
                  (let [[hs gs] rh]
                    (cond-> (membership/terms-of kb c hs)
                      gs (into (membership/terms-under kb w c (ground-ends kb gs))))))
          xs    (into full moves)
          lows  (into (set (:lows edge-moved)) flows)
          narrow (into #{} (remove #(or (contains? other %) (contains? moves %))) edged)
          under? (membership/under-lows w lows)
          plan? (fn [x] (when (contains? narrow x)
                          #(membership/reaches-lows? w recs under? %)))]
      ;; every term's routes are read before the first term's writes (`plan-sets`)
      (let [hs-of   #(into (set (get moved %)) (mapcat :members) (membership/nogoods-of c %))
            terms   (sort xs)
            ;; the nogoods each term's read ticks: its first batch (`plan-sets*`), and none
            ;; for a term outside `full` when the reach has no `:under`
            total   (transduce (map #(if (or (contains? full %) (:under reach))
                                       (min plan-batch (count (membership/nogoods-of c %)))
                                       0))
                               + xs)
            planned (tax/with-neighbours
                      (atom {})
                      (fn []
                        (with-open [r (progress/start ::plan-memberships
                                                      "settle: read the membership nogoods' routes" total)]
                          (mapv (fn [x]
                                  (let [ngs (membership/nogoods-of c x)
                                        hs  (hs-of x)
                                        f?  (contains? full x)]
                                    (plan-sets kb reach (when f? hs) (when-not f? hs) #(when (seq %) ngs)
                                               #(membership/kind-of w %1 %2) #(membership/routes w recs %)
                                               #(membership-owned? kb %1 %2) #(progress/tick! r)
                                               (plan? x))))
                                (cap/hinting (placement-hinter kb hs-of) placement-hint-chunk terms)))))]
        (let [placed (with-open [r (progress/start ::place-memberships "settle: place the membership nogoods"
                                                   (count planned))]
                       (into [] (mapcat (fn [[_ place!]] (place!)))
                             (progress/each r (cap/hinting (placement-hinter kb (comp hs-of first))
                                                           placement-hint-chunk (map vector terms planned)))))
              [readings seeds] (sync-edge-readings! kb c terms sup)]
          (vswap! minted into seeds)
          (into placed readings))))))

(defn- place-related!
  "Place the related-types nogoods whose placement can have moved, remove the placements
  of those gone, and return the handles created: the nogoods holding a declaration `moved`
  names (`related/take-moved!`), the pass relabelled (`fresh`) or a relabelled placement names
  (`placed`), those contradicted `orthogonal` with an argument under a separated type
  (`related/reread-separated!`), those holding a candidate a `genlCx` move reaches, and every
  one when a ground is stated where the move reaches (`reach-handles`).  Each is placed at
  its routes' placements (`related/routes`, `route-placements`)."
  [kb c moved reach grounds fresh placed]
  (let [holds? (:holds? related/family)
        tax    (reasoning/taxonomy kb)
        recs   (:records kb)
        w      (decide/unscoped-closures tax)
        ends   (into #{} (comp (keep #(tax/separation-ends tax %)) cat) (tax/supported-keys tax fresh))
        sep    (related/reread-separated! kb w ends)
        c      (if (seq sep) (decide/synced kb) c)
        rh     (reach-handles c reach grounds)
        full   (-> (set moved)
                   (into (filter #(holds? kb c %)) fresh)
                   (into (comp (filter #(related/kind-of w recs %)) cat) placed)
                   (into sep)
                   (into (when (= ::all rh) ((:handles related/family) kb c))))
        rhs    (when (vector? rh)
                 (if (second rh)
                   ((:handles related/family) kb c)
                   (filter #(holds? kb c %) (first rh))))]
    (when (or (seq full) (seq rhs))
      (place-sets! kb reach full rhs
                   #(into #{} (mapcat (fn [h] (related/nogoods-holding kb w c h))) %)
                   #(related/kind-of w %1 %2)
                   #(related/routes w recs %)
                   (fn [ms _] (boolean (related/kind-of w recs ms)))))))

(defn- unit-row-members
  "The tuple members naming a unit that a unit-table row among the handles `hs` declares
  (`provers/unit-table-predicates`): a determinant pair of two measures is excluded where
  `provers/measures-agree?` reads them as one value, and that reading moves with the
  table."
  [kb c hs]
  (let [recs  (:records kb)
        units (into #{} (keep (fn [h]
                                (let [s (some-> (p/get-sentex recs h) :sentence)]
                                  (when (and (seq? s) (contains? provers/unit-table-predicates (first s))
                                             (symbol? (second s)))
                                    (second s)))))
                    hs)]
    (into #{} (comp (mapcat #(reads/as-stored-with-term (:index kb) %)) (filter #(tuple/member? kb c %)))
          units)))

(defn- place-tuples!
  "Place the tuple nogoods whose placement can have moved, remove the placements of those
  gone, and return the handles created: the nogoods holding a member `moved` names
  (`tuple/take-moved!`), a member the pass relabelled (`fresh`) or a relabelled placement names
  (`placed`), a member naming a unit a relabelled unit-table row declares (`unit-row-members`),
  a member under a mark or `genl` edge among `fresh` (`tuple/members-under`, `mark-ends`), and
  a member a `genlCx` move reaches (`reach-handles`, `tuple/self-tuples-in`).  Each is placed
  at its routes' placements (`tuple/routes`, `route-placements`).  Reads nothing while the
  index keeps no member, no `irreflexive` mark is stored and nothing is queued."
  [kb c moved reach grounds fresh placed]
  (when (or (seq moved) (tuple/held? (reasoning/taxonomy kb) c))
    (let [tax  (reasoning/taxonomy kb)
          w    (decide/unscoped-closures tax)
          rh   (reach-handles c reach grounds)
          mem? #(tuple/member? kb c %)
          full (-> (set moved)
                   (into (filter mem?) fresh)
                   (into (filter mem?) placed)
                   (into (unit-row-members kb c fresh))
                   (into (tuple/members-under kb w c (mark-ends kb (grounds-of kb fresh))))
                   (into (when (= ::all rh) (tuple/members kb w c))))
          rhs  (when (vector? rh)
                 (let [[hs gs] rh]
                   (-> (filterv mem? hs)
                       (into (tuple/self-tuples-in kb w (:below reach)))
                       (cond-> gs (into (tuple/members-under kb w c (mark-ends kb gs)))))))]
      (when (or (seq full) (seq rhs))
        (place-sets! kb reach full rhs #(tuple/nogoods-holding kb c %) (constantly true)
                     #(tuple/routes kb w c % (partial provers/measures-agree? kb))
                     (fn [ms core] (tuple/owned? tax ms core)))))))

(defn- placed-pair-sets
  "The member sets of the placed arity pairs (`arity/kind-of`) that a nogood justification
  resting on the handle `h` concludes in CxUniverse with the two members as its only
  antecedents, the justification `sync-arity-pairs!` stores.  Another family's nogood over
  the same members carries its grounds, and is placed where both members are seen."
  [kb h]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (into #{} (keep (fn [jid]
                      (let [j (jtms/justification tms jid)
                            c (when (= nogood-informant (:informant j))
                                (p/get-sentex recs (:consequence j)))
                            s (:sentence c)]
                        (when (and (= sx/root-context (:context c)) (= 'contradicts (nm/functor s)))
                          (let [ms (into #{} (keep sx/handle-id) (rest s))]
                            (when (and (= ms (set (:antecedents j))) (arity/kind-of kb ms))
                              ms))))))
          (jtms/dependents tms h))))

(defn- sync-arity-pairs!
  "Place one `(contradicts …)` in CxUniverse for each arity pair at a predicate of `ps`
  (`{p dirs}`, `arity/drain!`'s `:pairs`, `arity/pair-sets`), justified by its two bindings, remove
  the placements of the pairs at it that no longer stand, and return the handles created.
  Both members are forced-monotonic, so the verdict places no `defeat`
  (`place-justified!`).  Under `:up`, a pair with a predicate below `p` is left to that
  predicate's own sync."
  [kb ps]
  (let [recs (:records kb)
        root sx/root-context
        key  (fn [ms] (vec (sort (map #(nm/print-key (:sentence (p/get-sentex recs %))) ms))))
        ;; `pair-sets`' closure answers, kept while no `genl` edge moves
        held (volatile! nil)
        memo (fn [] (let [tax (reasoning/taxonomy kb)
                          g   [(tax/relation-epoch tax) (tax/relation-gen tax :genl)]]
                      (when-not (= g (first @held)) (vreset! held [g (volatile! {})]))
                      (second @held)))]
    (with-open [r (progress/start ::sync-arity-pairs "settle: place the arity pairs" (count ps))]
      (reduce
       (fn [made [q dirs]]
         (let [want (arity/pair-sets kb q dirs (memo))
               have (cond->> (into #{} (mapcat #(placed-pair-sets kb %)) (arity/root-bindings kb q))
                      (= :up dirs) (into #{} (remove #(arity/below-pair? kb q % (memo)))))]
           (doseq [ms (sort-by key (remove want have))]
             (place-justified! kb ms [] #(= ms %)))
           (into made (mapcat #(place-justified! kb % [[root %]] (fn [core] (= % core))))
                 (sort-by key (remove have want)))))
       [] (progress/each r (sort-by (comp nm/print-key first) ps))))))

(defn- sync-negates-lengths!
  "Place one `(contradicts (sentexHandle d))` in the context of each stored `negates`
  declaration `d` IN in the network whose sides' lengths clash (`arity/negates-clash`),
  justified by `d` and the bindings stating the lengths, remove the placement of each one
  that no longer clashes, and return the handles created.  Reads the declarations
  `queued`, and those naming a term of `moved` (`arity/drain!`'s `:moved`, every stored
  declaration under `:all`).  The declaration is forced-monotonic, so the verdict places
  no `defeat` (`place-justified!`)."
  [kb queued moved]
  (let [tax   (reasoning/taxonomy kb)
        idx   (:index kb)
        sides (cond
                (not (tax/negates? tax)) nil
                (= :all moved)           :all
                :else                    (filter #(seq (tax/negates-of tax %)) moved))]
    (when (or (seq queued) (= :all sides) (seq sides))
      (let [recs  (:records kb)
            tms   (reasoning/tms kb)
            ds    (if (= :all sides)
                    (into (set queued) (reads/as-stored-with-functor idx 'negates))
                    (into (set queued)
                          (mapcat (fn [p] (concat (reads/as-stored-with-args idx 'negates {1 p})
                                                  (reads/as-stored-with-args idx 'negates {2 p}))))
                          sides))
            owns? (fn [core] (boolean (some #(arity/binding-handle? kb %) core)))]
        (into []
              (mapcat (fn [sx]
                        (let [d     (:id sx)
                              clash (when (jtms/network-in? tms d)
                                      (arity/negates-clash kb (:sentence sx)))]
                          (place-justified! kb #{d}
                                            (if clash [[(:context sx) (conj (:grounds clash) d)]] [])
                                            owns?))))
              (nm/sort-by-content-key (juxt :sentence :context) nm/compare-form
                                      (keep #(p/get-sentex recs %) ds)))))))

(defn placement-queued?
  "Has the negation, membership, related-types, tuple or arity index queued a nogood the
  settle places again (`negation/take-moved!`, `membership/take-moved!`,
  `related/take-moved!`, `tuple/take-moved!`), or does the arity or the argument family
  owe a refresh (`arity/moved?`, `argument/moved?`)?  A rebuilt index
  queues every standing one (`recover`).  The negation family keeps no candidate rows:
  after a rebuild every pair is owed while a body is stored in both polarities
  (`decide/placements-owed?`, `reads/stores-opposed?`)."
  [kb]
  (let [c (decide/synced kb)]
    (or (negation/moved? c)
        (and (decide/placements-owed? c) (reads/stores-opposed? (:index kb)))
        (membership/moved? c) (related/moved? c) (tuple/moved? c)
        (arity/moved? (reasoning/taxonomy kb) c) (arity/classes-queued? (reasoning/taxonomy kb) c)
        (argument/moved? (reasoning/taxonomy kb) c (special/conviction-generations kb)))))

(def ^:private forced-declaration-kinds
  "The forced-monotonic property each declaration functor gives its predicate."
  '{forced_monotonic_predicate          :forced-monotonic
    forced_monotonic_between_predicates :forced-between-predicates})

(defn- declarations-in
  "The forced-monotonic declarations stored in a context of `ctxs`, belief unread."
  [kb ctxs]
  (when (seq ctxs)
    (into [] (mapcat #(reads/as-stored-with-functor-in (:index kb) % ctxs))
          (sort (keys forced-declaration-kinds)))))

(defn declaration-reach
  "The facts whose nogoods' verdicts and whose readings the forced-monotonic declaration
  `s` stated in `c` moves, or nil when `s` declares no predicate outside the baseline set
  (`decide/global?`): the stored facts of its predicate, and the stored denials of them a
  negation pair holds, stated in a context that a context at or below `c` sees
  (`tax/contexts-seen-with-global`).  The closures are unscoped: a placement reads the
  network, a superset over every reader (`decide/unscoped-closures`)."
  [kb s c]
  (let [tax  (reasoning/taxonomy kb)
        recs (:records kb)
        idx  (:index kb)
        kind (when (and (seq? s) (= 2 (count s)) (symbol? (second s)))
               (forced-declaration-kinds (first s)))
        pred (when kind (second s))]
    (when (and pred (symbol? c) (not (decide/global? tax kind pred)))
      (let [seen (tax/contexts-seen-with-global
                  tax c (first (reads/as-stored-contexts-with-functor-global idx pred)))]
        (when (seq seen)
          (concat (reads/as-stored-with-functor-in idx pred seen)
                  (filter #(let [d (:sentence (p/get-sentex recs %))]
                             (and (sx/negation? d) (= pred (nm/functor (second d)))))
                          (when (reads/stores-opposed? idx)
                            (reads/as-stored-opposed-in idx seen)))))))))

(defn- declared-reach
  "`declaration-reach` of each stored forced-monotonic declaration among the handles `hs`."
  [kb hs]
  (let [recs  (:records kb)
        ;; the functor postings narrow `hs` before a record is read: a recover's region is
        ;; every stored handle, and a network record store fetches each in a round trip
        decl? (into #{} (mapcat #(reads/as-stored-with-functor (:index kb) %))
                    (keys forced-declaration-kinds))]
    (with-open [r (progress/start ::declared-reach "settle: read the forced declarations' reach"
                                  (count hs))]
      (into #{} (comp (filter decl?)
                      (mapcat #(let [{s :sentence c :context} (p/get-sentex recs %)]
                                 (declaration-reach kb s c))))
            (progress/each r hs)))))

(defn place-inherited!
  "Find the inherited clashes (`discovery/discover-inherited!`) and place each at its
  vantages, the most general contexts that read it whole, justified by its members and the
  `genlCx` edges each vantage sees them over; remove the placements of each member set no
  longer found (`place-justified!`), in content order.  Returns the handles created.  A clash
  whose memo entry was carried keeps its placements unless a member is among the facts a
  moved forced-monotonic declaration reaches (`declared-reach`).  `moves` is the pass's
  `genlCx` moves (`special/drain-context-moves!`).  See docs/nmtms.md, \"A `recover` places
  the nogoods its store does not hold\"."
  [kb region {:keys [reach first?]}]
  (let [;; a forced-monotonic declaration arriving, or stated where a `genlCx` move reaches, moves
        ;; the verdicts of the clashes over its predicate's facts (`declared-reach`)
        moved (when (seq (decide/declared (reasoning/taxonomy kb)))
                (declared-reach kb (into (vec @region) (declarations-in kb (:below @reach)))))
        {:keys [found left]} (discovery/discover-inherited! kb region reach first? moved)
        tax   (reasoning/taxonomy kb)
        recs  (:records kb)
        owns? (fn [ms] (let [ms (set ms)] #(= ms %)))]
    (-> []
        (into (mapcat #(place-justified! kb % [] (owns? %)))
              (nm/sort-by-content-key #(content-key kb %) nm/compare-form left))
        (into (mapcat (fn [{ms :nogood vs :vantages}]
                        (let [ctxs (into [] (comp (map #(:context (p/get-sentex recs %))) (distinct)) ms)]
                          (place-justified! kb ms
                                            (for [v (sort vs)]
                                              [v (into (set ms) (visibility-support tax v ctxs))])
                                            (owns? ms)))))
              (nm/sort-by-content-key #(content-key kb (:nogood %)) nm/compare-form found)))))

(defn place-nogoods!
  "Place, once a settle pass, the nogoods of the families placed as conclusions whose
  placement can have moved since the last call: `{:made [h …] :minted [h …] :released [h …]}`.
  `:made` holds the handles created (`place-negations!`, `place-memberships!`,
  `place-related!`, `place-tuples!`, after the arity family's refresh `arity/drain!`,
  `sync-arity-pairs!`); `:minted` the chaining seeds of the mints a type's length admitting one
  again owes (`special/mints-on-lengths`); `:released` the handles the argument-hold and arity
  refreshes took out of `:out`, for the settle to re-chain (`jtms/revived`).  Every family
  detects over the network's IN label (`jtms/network-in?`).  Each family reads what its
  write-time index queued, the handles among `region` (a delay) that `read` (a volatile set)
  does not hold yet, the handles an except of which moved and what rests on them, and what
  the pass's `genlCx` moves reach (`moves`' `:reach`).  Reads nothing while no family holds a
  nogood or queued one and no `orthogonal` is stored."
  [kb region read {:keys [reach first?]}]
  (let [c (decide/synced kb)
        bodies (negation/take-moved! kb)
        mmoved (membership/take-moved! kb)
        medges (membership/take-edge-moved! kb)
        rmoved (related/take-moved! kb)
        tax    (reasoning/taxonomy kb)
        ;; a family that keeps no nogood places nothing, and a queued handle then matters
        ;; only for the placements it holds, which the family removes
        tms     (reasoning/tms kb)
        holds?  (fn [h] (some #(= nogood-informant (:informant (jtms/justification tms %)))
                              (jtms/dependents tms h)))
        placing (fn [held? moved] (if held? moved (into #{} (filter holds?) moved)))
        tmoved (placing (tuple/held? tax c) (tuple/take-moved! kb))
        ;; the arity refresh alone runs the other families' placement reads for nothing
        others? (or (reads/stores-opposed? (:index kb)) (seq (:terms mmoved)) (seq (:terms medges))
                    (seq (membership/nogoods-terms c))
                    (seq rmoved) (related/orthogonals? kb (decide/unscoped-closures tax))
                    (seq tmoved) (tuple/held? tax c) (related/held? kb c))]
    (when (or others? (arity/moved? tax c) (arity/relabel-owed? kb (remove @read @region))
              (argument/moved? tax c (special/conviction-generations kb)))
      (let [;; the `:below` walk is quadratic in a chain of edges moved in one pass
            reach  (when others? @reach)
            ;; what the move reaches through the grounds, read once for the three families
            grounds (delay (reach-grounds kb reach))
            fresh  (into [] (comp (distinct) (remove @read)) @region)
            _      (vswap! read into fresh)
            ;; an except arriving or leaving moves a placement with no relabel of the
            ;; handle it names or of what rests on it (`special/except-moved`, its
            ;; consequence closure), drained once a pass
            _      (arity/note-relabelled! kb fresh)
            _      (when (argument/declares-any? tax)
                     (argument/note-relabelled! kb (into [] (keep #(p/get-sentex (:records kb) %))
                                                         (arity/relabelled-held kb fresh))))
            ;; the argument holds, before the families that detect over the network
            released (volatile! (vec (checks/refresh-argument-holds! kb (special/conviction-generations kb))))
            fresh  (into fresh (remove (set fresh))
                         (jtms/consequence-closure (reasoning/tms kb) (special/except-moved kb)))
            ;; a forced-monotonic declaration arriving, or stated where a `genlCx` move reaches,
            ;; moves the verdicts over its predicate's facts with no relabel of them
            fresh  (if others?
                     (into fresh (remove (set fresh))
                           (declared-reach kb (into fresh (declarations-in kb (:below reach)))))
                     fresh)
            psets  (when others? (placed-members kb fresh))
            placed (into #{} cat psets)
            minted (volatile! [])
            made   (binding [*witnesses* (volatile! nil)]
                     (-> []
                         ;; first, since a tuple the refresh holds inert is OUT in the
                         ;; network every other family detects over
                         (into (let [{:keys [pairs moved bound] freed :released} (arity/drain! kb)]
                                 (vswap! released into freed)
                                 (special/recheck-on-lengths kb moved)
                                 ;; the declarations and facts naming a type whose own
                                 ;; length admits one again mint now
                                 (vreset! minted (:new (special/mints-on-lengths kb bound)))
                                 ;; ...and a type bound to another length drops its
                                 ;; declarations' entailments and mints
                                 (when-let [jids (seq (concat (special/withdrawn-type-entailments kb (keys bound))
                                                              (special/withdrawn-type-mints kb bound)))]
                                   (drop-justifications! kb jids))
                                 (into (sync-arity-pairs! kb pairs)
                                       (sync-negates-lengths! kb (arity/take-negates! kb) moved))))
                         (cond-> others?
                           (-> (into (place-negations! kb bodies reach first? fresh placed))
                               (into (place-memberships! kb c mmoved medges reach grounds fresh placed minted))
                               (into (place-related! kb c rmoved reach grounds fresh psets))
                               (into (place-tuples! kb c tmoved reach grounds fresh placed))))))]
        ;; a placement this pass created is relabelled by its creation alone, so the next
        ;; pass does not read it as moved and place its nogood again
        (vswap! read into made)
        {:made made :minted (special/minted-seeds kb @minted) :released @released}))))

;; ---- a refused firing is remembered as bindings --------------------------
;;
(defn- refusal-reason
  "Why a completed firing may not be placed in `pctx`, or nil: `:post-join`, `:naf`,
  `:separation`, `:entailment`, `:hidden` or `:mention` (`mention-unread?`), cheapest first.
  `:naf` is a closed-extent negative antecedent that does not hold or a `different`
  antecedent that fails in `pctx` (`different-blocks?`); `:separation` a `disjoint`
  antecedent the join read separated and `pctx` does not (`separation-exempted?`);
  `:entailment` an antecedent on a calculus predicate naming a node of an unsatisfiable
  component at `pctx` (`antecedent-blocked?`).  An `exceptWhen` or `(unknown S)` that holds
  refuses nothing.  `bindings` is nil when a post-join literal had none or several answers."
  [kb rule antes bindings pctx]
  (cond
    (nil? bindings)                                                  :post-join
    (closed-extent-blocks? kb (:closed-extent rule) bindings pctx)   :naf
    (different-blocks? kb (:different rule) bindings pctx)           :naf
    (separation-exempted? kb (:antecedents rule) bindings pctx)      :separation
    (and (seq (antecedent-calculi kb (:antecedents rule)))
         (antecedent-blocked? kb (:antecedents rule) (delay bindings) pctx)) :entailment
    (antecedent-hidden? kb antes pctx)                               :hidden
    (mention-unread? kb (:antecedents rule) bindings pctx)           :mention))

(def ^:dynamic *report-no-placement?*
  "Whether a completed firing that finds no placement context files a `:no-placement`
  entry.  True wherever content arrives.  False for the re-chain a teardown owes
  (`core/settle-after-teardown!`), which re-asks firings the removal already swept and
  would otherwise fill the ledger (cap 1000) and log a `:warn` line apiece."
  true)

(defn- placement-antecedents
  "The antecedents a firing's placement reads, as `[handles records]`: all of `handles`
  (with `facts`, their records) but a permuting-mark statement the firing names without having
  matched it (`read-marks`, `inherit/claim-supports`).  The firing names the mark so that
  retracting it withdraws the firing.  The matcher reads the mark from every context, so a
  firing placed by the mark's context would find no placement in a context that sees no
  statement of it.  A mark statement the rule matched as an antecedent is a matched
  fact and places the firing."
  [handles facts matched]
  (let [read-mark? (fn [sxr]
                     (let [s (:sentence sxr)]
                       (and (sequential? s) (inherit/permuting-mark? (first s)))))]
    (if-not (some read-mark? facts)
      [handles facts]
      (let [hit  (into #{} (map second) matched)
            keep (keep-indexed (fn [i h]
                                 (let [sxr (nth facts i)]
                                   (when (or (contains? hit h) (not (read-mark? sxr)))
                                     [h sxr])))
                               handles)]
        [(mapv first keep) (mapv second keep)]))))

(defn- restates-an-antecedent?
  "Is `conclusion` the stored sentence of one of `facts`, the records a firing's
  placement reads?  Such a firing places nothing and stores no justification: every
  placement context sees the fact, and a justification resting on its own conclusion
  never brings it IN.  Compared as substituted, so a symmetric conclusion spelled as the
  fact's mirror is not caught.  See docs/inference.md, \"A firing whose conclusion is
  one of the facts it matched\"."
  [conclusion facts]
  (boolean (some #(= conclusion (:sentence %)) facts)))

(defn- owe-batch-rejoin
  "Note in `owed`, a batch's `*batch-rejoins*` map, that the rule at `rh` re-joins at the
  batch's settle: kept to the rows resting on a handle of `delta`, or every row when
  `delta` is nil or the rule owes every row already."
  [^java.util.Map owed rh delta]
  (let [cur (.get owed rh)]
    (.put owed rh (if (and delta (not= :all cur)) (into (or cur #{}) delta) :all))))

(defn- unrestated-placements
  "The contexts of `placements` whose taxonomy does not hold `conclusion`, `(C x)`, from a
  fact `(T x)`, `T` one of `ts` (`lazy-membership-types`): those whose `genls` of each `T`
  holds no `C`.  Inside a `with-deferred-settle` batch, a firing with such a context
  places nothing and owes the rule at `rh` a re-join at the batch's settle, kept to the
  rows on `handles` (`owe-batch-rejoin`).  `placements` when `ts` is empty.  See
  docs/inference.md, \"A lazy-forward rule\"."
  [kb conclusion ts rh handles placements]
  (if (empty? ts)
    placements
    (let [c    (first conclusion)
          tx   (reasoning/taxonomy kb)
          open (into [] (remove (fn [pctx] (some #(contains? (tax/genls tx % pctx) c) ts))) placements)]
      (if-let [owed (when (and (seq open) wiring/*defer-settle?*) *batch-rejoins*)]
        (do (owe-batch-rejoin owed rh handles) [])
        open))))

(defn- unconverse-placements
  "The contexts of `placements` in which a firing concluding `conclusion` over the rule
  antecedents `antes`, whose placement reads `facts`, does not prove a lazy literal by the
  converse of its reader's lazy reading (`converse-lazy-reading?`); `placements` when
  `facts` hold no lazy-forward rule's record."
  [kb conclusion antes facts placements]
  (if-let [lz (seq (filter #(some-> % rules/lazy-sentex?) facts))]
    (into [] (remove #(converse-lazy-reading? kb (nm/functor conclusion) antes lz %)) placements)
    placements))

(defn- place-conseq
  "Place one ground conclusion literal `conseq` from a firing in each maximal context that sees
  the rule and all antecedent facts, unless the rule's exception, a NAF antecedent or the
  context's taxonomy (`unrestated-placements`) blocks it there.  Returns the new handles.  A
  firing with no placement context is recorded as a dropped conclusion; one refused by a
  re-checkable block condition is recorded as a refusal.  `links` are the firing's subsumptions
  (`subsumption-links`), an ingredient of the placement (`placement-ingredients`), and join the
  antecedent list with the `genlCx` supporters.  `strict` is the links a negated antecedent
  climbed (`placements-over`).  `placed` is `[handles records]` of the antecedents the
  placement reads (`placement-antecedents`); `handles` is all of them."
  [kb rule conseq handles placed all-antes links strict depth max-depth bindings]
  (let [[phs facts]          placed
        subs                 (when (seq links) (set links))
        fact-ctxs            (map :context facts)
        [placements support] (placement-ingredients kb rule links phs fact-ctxs strict)]
    (if (empty? placements)
      ;; The join completed and then no context sees everything the firing rests on.  "Possibly
      ;; none" is a legitimate outcome of `maximal-common-descendant-contexts`, so it is recorded
      ;; like any other dropped conclusion, naming the subsumption when there was one and
      ;; recomputing the contexts that would have taken it but for the edges (drop path only).
      ;; A teardown's re-chain asks and is not told: `*report-no-placement?*`.
      (do (when *report-no-placement?*
            (violations/report kb
                               [{:violation :no-placement :sentence conseq :rule (:rule-handle rule)
                                 :detail (cond-> {:rule-context  (:context rule)
                                                  :fact-contexts (vec (distinct fact-ctxs))
                                                  :message
                                                  ;; the remedy, not only the diagnosis, for facts asserted into a context with no edge to the one holding the rule
                                                  (if (seq links)
                                                    (str "completed firing has no placement context — "
                                                         "no context sees the rule, all antecedent facts, "
                                                         "and the genl edges the match subsumed through.  "
                                                         "Add the genlCx edges that put one context "
                                                         "above all of them (:rule-context and "
                                                         ":fact-contexts below name what has to be seen, "
                                                         ":subsumed the edges)")
                                                    (str "completed firing has no placement context — "
                                                         "no context sees the rule and all antecedent facts.  "
                                                         "Add the genlCx edges that put one context "
                                                         "above both (:rule-context and :fact-contexts "
                                                         "below name what has to be seen)"))}
                                           (seq links)
                                           (assoc :subsumed (mapv first links)
                                                  :would-place
                                                  (vec (tax/maximal-common-descendant-contexts
                                                        (reasoning/taxonomy kb)
                                                        (cons (:context rule) fact-ctxs)))))}]))
          [])
      ;; `exceptWhen`, `unknown` and a visibility `except` block per placement, since each is
      ;; evaluated in the conclusion's context: a firing that placed would leave no conclusion
      ;; and no justification.  `all-antes` includes the rule handle, so a hidden rule does not
      ;; fire into the ancestor set.  `mapcat`: one placement yields the conclusion and a copy
      ;; in each context the predicate is lifted into, each a new datum for the agenda.
      (into []
            (mapcat (fn [pctx]
                      ;; the taxonomy supporters are per placement, so the antecedent list is too, and this list
                      ;; is what the `except` check reads, as `justification-excepted?` reads the stored
                      ;; justification's antecedents.  Arrival order here, content order at the point of storing
                      ;; (`kb/antecedent-order`): nothing between here and the store reads a position
                      ;; (`antecedent-hidden?` is a `some`, the dedup is set-keyed), so the sort moves to the
                      ;; refusal record and `place-conclusion`, and a refused or re-deriving firing pays no sort.
                      (let [antes (into all-antes (get support pctx))
                            post  (:post-join rule)
                            ;; the post-join literals extend the bindings every check
                            ;; below reads, in the conclusion's own context
                            bindings (if (seq post)
                                       (post-join-bindings kb post bindings pctx)
                                       bindings)
                            ;; the post-join literals may have bound a consequent
                            ;; variable the join left open
                            c (when bindings
                                (cond-> conseq (seq post) (res/substitute bindings)))]
                        (if-let [why (refusal-reason kb rule antes bindings pctx)]
                          (when (#{:naf :separation :entailment :mention} why)
                            ;; a refusal entry is deduplicated by value and `release-refusal!` hands its `:antes` to `place-conclusion`, so it is content-ordered here
                            (record-refusal! kb rule c pctx (kb/antecedent-order kb antes)
                                             bindings max-depth (when subs {:subsumptions subs}))
                            nil)
                          (place-conclusion kb rule c pctx antes depth bindings
                                            (:strength rule) subs)))))
            (unrestated-placements kb conseq (lazy-membership-types conseq facts)
                                   (:rule-handle rule) handles
                                   (unconverse-placements kb conseq (:antecedents rule) facts
                                                          placements))))))

(defn- nesting-under
  "`term-nesting` of `t` measured inside the constants `path`.  A constant on `path` met
  again counts 1 and sets `cycle`, and a value whose measure set it is not kept in `memo`,
  so every value `memo` holds is the same from whichever term it was reached."
  [kb ^java.util.Map memo path cycle t]
  (cond
    (sequential? t)
    (inc (long (reduce (fn [^long m a] (max m (long (nesting-under kb memo path cycle a)))) 0 (rest t))))

    (nat-read/reified-nat-symbol? t)
    (cond
      (.containsKey memo t) (long (.get memo t))
      (contains? path t)    (do (vreset! cycle true) 1)
      :else
      (let [inner (volatile! false)
            n     (if-let [e (nat/nat-expression kb t)]
                    (max 1 (long (nesting-under kb memo (conj path t) inner e)))
                    1)]
        (if @inner (vreset! cycle true) (.put memo t n))
        n))

    :else 0))

(defn- term-nesting
  "How deeply term `t` nests function applications: 0 for an atom, one more than its
  deepest argument for a compound, and for a reified constant the nesting of the
  expression its `natFormula` names, or 1 when none is stored.  A constant met again
  inside its own expression, which two merged formulas can make, counts 1 there.  `memo`
  is one firing's (`term-cut?`), so each firing reads the formulas stored when it fires."
  ^long [kb memo t]
  (long (nesting-under kb memo #{} (volatile! false) t)))

(defn- sentence-nesting
  "The deepest `term-nesting` among the arguments of `s`'s literals
  (`nm/applied-literals`).  A sentence wrapper (`not`, `and`, `ist`, a rule) adds no
  level, so a conclusion and the facts it rests on are measured alike."
  ^long [kb memo s]
  (reduce (fn [^long m [_ lit]]
            (reduce (fn [^long m a] (max m (term-nesting kb memo a))) m (rest lit)))
          0 (nm/applied-literals s)))

(defn- ground-nesting
  "The deepest `term-nesting` among the ground subterms of rule template `form`: a term
  written in the rule, as opposed to a term the rule builds around a variable."
  ^long [kb memo form]
  (cond
    (sx/variable? form) 0
    (sequential? form)  (if (sx/ground-term? form)
                          (term-nesting kb memo form)
                          (reduce (fn [^long m a] (max m (ground-nesting kb memo a))) 0 (rest form)))
    :else               (term-nesting kb memo form)))

(defn- builds-terms?
  "Does consequent template `form` apply a function to a variable in an argument
  position?  Only such a rule, or one with a head existential, can conclude a term deeper
  than every term its firing rests on (`term-cut?`)."
  [form]
  (boolean (some (fn [[_ lit]] (some #(and (sequential? %) (not (sx/ground-term? %))) (rest lit)))
                 (nm/applied-literals form))))

(defn- term-cut?
  "Is the firing of `rule` at `bindings` over the records `facts`, concluding `built`
  (the substituted consequent, with each head existential replaced by its unminted
  `SkolemFn` expression), past the run's term-nesting bound (`*term-bound*`)?  It is when
  `built` nests terms deeper than the bound and deeper than every term the firing rests
  on: the matched facts, the binding values and the ground terms the rule writes.  A rule
  passing an asserted deep term through is never cut.  The answer is a function of the
  firing's content, the formulas its constants name when it fires, and the bound."
  [kb {bound :max} rule bindings facts built]
  (let [memo (java.util.HashMap.)
        c    (sentence-nesting kb memo built)]
    (and (> c (long bound))
         (let [rests-on (reduce (fn [^long m v] (max m (term-nesting kb memo v)))
                                (max (ground-nesting kb memo (:consequent rule))
                                     (reduce (fn [^long m f]
                                               (if f (max m (sentence-nesting kb memo (sx/sentence-of f))) m))
                                             0 facts))
                                (vals bindings))]
           (> c rests-on)))))

(defn- derive-conclusion
  "Record one rule firing at the rule's own justification strength (`:strength`,
  `provers/firing-strength`), placed in the maximal contexts that see the rule and all
  antecedent facts; returns `{:new [handles]}`.  The rule handle is part of the justification.
  A default conclusion is placed unconditionally; any defeat is decided at settle.  A head
  existential `(exists ?y C)` is skolemized before placement (docs/skolem.md).  A firing past
  `max-depth`, or reached once `*stop*` is, places nothing and marks the run truncated; a firing
  past the term-nesting bound (`term-cut?`) is counted in `:term-cut`.  Each firing runs
  `heap-check!`."
  [kb rule {:keys [bindings handles matched]} max-depth truncated]
  (heap-check!)
  (let [tms   (reasoning/tms kb)
        depth (inc (long (reduce (fn [d h] (max (long d) (long (jtms/depth tms h)))) 0 handles)))]
    (if (or (and max-depth (> depth (long max-depth))) (stopped? *stop*))
      (do (reset! truncated true) (when *tick* (*tick* 0)) {:new []})
      (let [raw0 (res/substitute (:consequent rule) bindings)
            ;; existential head variables are the ones still unbound here, less a post-join
            ;; literal's output; a generator's head is not skolemized (docs/generators.md)
            free (when-not (rules/rule-sentence? (peek (sx/peel-rule-wrapper raw0)))
                   (let [f (free-consequent-vars raw0)]
                     (if-let [post (seq (:post-join rule))]
                       (seq (remove (into #{} (mapcat sx/deferred-output-vars) post) f))
                       f)))
            wits (when free (skolem/witnesses rule bindings free))
            ;; the matched records, fetched once: placement reads their contexts, the
            ;; subsumption links read their antecedent keys, and the term bound their
            ;; sentences
            facts (mapv #(p/get-sentex (:records kb) %) handles)
            tb   *term-bound*]
        (if (and tb (or free (:builds-terms? rule))
                 (term-cut? kb tb rule bindings facts
                            (cond-> raw0 wits (res/substitute (into {} wits)))))
          (do (vswap! (:cut tb) inc) (when *tick* (*tick* 0)) {:new []})
          (let [raw       (if free (skolem/skolemize-conclusion kb raw0 wits) raw0)
                ;; a ground `(Quasiquote T)` in the fired head constructs its `(Quote E)` mention here,
                ;; and `reify-conclusion` mints it (`quasiquote/any-quasiquote?`)
                raw       (quasiquote/maybe-reduce kb raw)
                placed    (placement-antecedents handles facts matched)
                ;; a conjunctive skolemized head shares one witness across its conjuncts
                ;; (only a head existential stores a conjunctive consequent — an ordinary
                ;; one is split by `expand-consequent` before storage)
                conjuncts (into [] (remove #(restates-an-antecedent? % (second placed)))
                                (if (and (sequential? raw) (= sx/and-functor (first raw)))
                                  (rest raw) [raw]))
                new       (when (seq conjuncts)
                            (let [all-antes (conj (vec handles) (:rule-handle rule))
                                  ;; a handle's record, read off the two aligned vectors: a
                                  ;; firing has a handful of antecedents, and a map built per
                                  ;; firing to look them up costs more than scanning them
                                  record-of (fn [h] (loop [i 0]
                                                      (when (< i (count facts))
                                                        (if (= h (nth handles i)) (nth facts i) (recur (inc i))))))
                                  links     (subsumption-links kb matched record-of)
                                  read      (edge-read-links kb matched record-of links)
                                  strict    (cond-> (negated-links kb matched record-of links)
                                              read (-> (or #{}) (into read)))
                                  rule      (cond-> rule (some declaration-record? facts) (assoc :inherited? true))
                                  place     #(reduce (fn [acc c]
                                                       (into acc (place-conseq kb rule c handles placed all-antes links
                                                                               strict depth max-depth bindings)))
                                                     [] conjuncts)]
                              (if read (binding [*report-no-placement?* false] (place)) (place))))]
            ;; a firing is the finest unit of work, so a long datum reports from here, including a firing that placed nothing
            (when *tick* (*tick* (count new)))
            ;; ...and where a shutdown stops a write: the firing's records and justifications
            ;; have all landed
            (dur/check-abort!)
            ;; a placed preservation declaration changes what every later join may inherit
            (note-placed-declaration! conjuncts)
            {:new (or new [])}))))))

(defn rule-fields-of
  "The fields the chainer reads of a rule sentex.  `:strength` is the justification class
  its firings confer (`provers/firing-strength`)."
  [kb handle rsx]
  (let [antes    (:antecedent rsx)
        watched? (reads/watched-rule? (:index kb) handle)]
    {:name handle :rule-handle handle :context (:context rsx)
     :antecedents antes :consequent (:consequent rsx) :watched? watched?
     :strength (provers/firing-strength kb handle rsx watched? nil)
     ;; the `exceptWhen` exceptions, `{:context :query}` per believed meta-sentex naming this
     ;; rule, block-if-any (`provers/rule-exception-entries`); fetched only when the
     ;; watched-rule set holds the rule (docs/exceptions.md)
     :excepts (when watched? (provers/rule-exception-entries kb handle))
     ;; the negation-as-failure antecedents — `(unknown S)` literals, blocked the same
     ;; way an exception is, per placement context (docs/naf.md)
     :naf (rules/naf-antecedents rsx)
     ;; ...and the negative antecedents a `closed_extent_predicate` grant reads as NAF —
     ;; withheld from the join and decided here, for the same reason and by the same
     ;; block/sweep/revive path (docs/naf.md)
     :closed-extent (closed-extent-antecedents kb antes)
     ;; the `different` antecedents, withheld from the join and decided per placement
     :different (rules/different-antecedents rsx)
     ;; the aggregates and what reads their output, which run per placement
     :post-join (rules/post-join-antecedents rsx)
     ;; whether a firing can build a term the term-nesting bound reads (`term-cut?`)
     :builds-terms? (builds-terms? (:consequent rsx))}))

(defn- rule-fields [kb handle]
  (rule-fields-of kb handle (p/get-sentex (:records kb) handle)))

;; ---- reading the refusal record back ------------------------------------

(defn refusals
  "What is recorded against rule `rh`: a set of refusal entries, `:overflow`, or nil.
  `settle` reads this to decide which firings a queued rule owes a re-ask."
  [kb rh]
  (get @(reasoning/refused kb) rh))

(defn drop-refusal!
  "Retire one entry.  A refusal is dead when it fires, when its rule goes, or when the
  antecedents behind its bindings are no longer believed — the bindings are a snapshot,
  and a refusal must not resurrect a firing whose support left.  An `:overflow` record
  holds no entries to drop."
  [kb rh entry]
  (swap! (reasoning/refused kb)
         (fn [m]
           (let [cur (get m rh)]
             (if (set? cur)
               (let [cur' (disj cur entry)]
                 (if (empty? cur') (dissoc m rh) (assoc m rh cur')))
               m)))))

(defn- refusal-live?
  "Is there still a firing for refusal `entry` of the rule stored as `rsx` to make —
  the rule a believed forward rule, and every antecedent stored and believed?"
  [kb rsx entry]
  (let [rec (:records kb)
        tms (reasoning/tms kb)]
    (and rsx (rules/rule? rsx) (rules/forward-sentex? rsx)
         (every? (fn [h] (and (p/get-sentex rec h) (jtms/in? tms h)))
                 (:antes entry)))))

(defn refusal-state
  "Re-decide one recorded refusal of rule `rh`, from scratch: `:dead` when there is no
  longer a firing to make, `:blocked` when the condition that refused it still holds, `:free`
  when it does not and the conclusion is owed a placement.  The judgement is
  `rule-firing-blocked?` plus the visibility `except` check.  Bindings are settled to the
  representatives `pctx` now elects first (`settled-bindings`)."
  [kb rh entry]
  (let [rsx (p/get-sentex (:records kb) rh)]
    (if-not (refusal-live? kb rsx entry)
      :dead
      (let [pctx (:pctx entry)]
        (cond
          (or (antecedent-hidden? kb (:antes entry) pctx)
              (rule-firing-blocked? kb rsx
                                    (delay (settled-bindings kb (:bindings entry) pctx))
                                    pctx))
          :blocked

          :else :free)))))

(defn rule-firing-report
  "Per forward rule in the KB: how many firings it placed, how many it refused and why, or
  whether it did nothing (docs/web.md).  Rules come off the antecedent keys
  (`:rule-antecedents`) and the rule index, so the cost is O(rules); the counts come from
  `jtms/dependents` and the refusal ledger (`refusals`, `refusal-state`).  Each row is `{:rule
  :sentence :believed? :placed :void :refused :refusals :status}`.  `:void` counts firings the
  forced-monotonic set holds void; `:placed` those neither void nor concluding a sentex the
  argument hold keeps OUT (`argument/held?`); `:refused` is `:overflow` or the entry count.
  `:refusals` is one map per recorded refusal (`:state`, `:reason`, `:conseq`, `:context`), then
  one `:blocked` map with reason `:constraint` per conclusion the argument hold keeps OUT, or
  nil.  `:status` is `:fires`, `:blocked` or `:silent`.  A conclusion dropped for a violation
  is in `violations`, not here."
  [kb]
  (let [rec (:records kb)
        tms (reasoning/tms kb)
        idx (:index kb)
        rule-hs (into (sorted-set) (reads/as-stored-rules-in-global idx :rule))
        void    (jtms/forced-members tms :void)]
    (into []
          (keep (fn [rh]
                  (when-let [rsx (p/get-sentex rec rh)]
                    (when (rules/forward-sentex? rsx)
                      (let [deps    (jtms/dependents tms rh)
                            voided  (count (filter void deps))
                            held    (into [] (comp (remove void)
                                                   (keep #(let [c (:consequence (jtms/justification tms %))]
                                                            (when (argument/held? kb c) (p/get-sentex rec c)))))
                                          deps)
                            placed  (- (count deps) voided (count held))
                            ref     (refusals kb rh)
                            over?   (= :overflow ref)
                            rfields (delay (rule-fields-of kb rh rsx))
                            entries (when (set? ref)
                                      (mapv (fn [e]
                                              (let [st (refusal-state kb rh e)]
                                                {:state   st
                                                 :reason  (when (= :blocked st)
                                                            (refusal-reason
                                                             kb @rfields (:antes e)
                                                             (when (:bindings e)
                                                               (settled-bindings kb (:bindings e) (:pctx e)))
                                                             (:pctx e)))
                                                 :conseq  (:conseq e)
                                                 :context (:pctx e)}))
                                            ref))
                            entries (cond-> entries
                                      (seq held)
                                      (-> vec (into (->> (distinct held)
                                                         (map (fn [csx] {:state :blocked :reason :constraint
                                                                         :conseq (sx/sentence-of csx)
                                                                         :context (:context csx)}))
                                                         (nm/sort-by-content-key (juxt :conseq :context))))))]
                        {:rule      rh
                         :sentence  (sx/authored-sentence rsx)
                         :believed? (boolean (jtms/in? tms rh))
                         :placed    placed
                         :void      voided
                         :refused   (if over? :overflow (count entries))
                         :refusals  entries
                         :status    (cond (pos? placed)                          :fires
                                          (or over? (seq entries) (pos? voided)) :blocked
                                          :else                                  :silent)}))))
                rule-hs))))

(defn release-refusal!
  "Re-derive the refused firing `entry` of rule `rh` and retire the entry, or retire it
  without deriving anything when its support has left.  Returns the handles created, for the
  caller to put back on the agenda.  Calls `place-conclusion` with the recorded bindings and
  never a fresh join, so k refusals cost k placements.  The depth is recomputed from the
  antecedent facts.  Re-decided here, since the sweep runs between the caller's scan and
  this call."
  [kb rh entry]
  (case (refusal-state kb rh entry)
    :blocked []
    :dead    (do (drop-refusal! kb rh entry) [])
    :free    (let [rule  (cond-> (rule-fields kb rh)
                           (some #(declaration-record? (p/get-sentex (:records kb) %)) (:antes entry))
                           (assoc :inherited? true))
                   depth (inc (reduce max 0 (map #(jtms/depth (reasoning/tms kb) %) (:handles entry))))
                   ;; the derivation-depth bound the refusing run was configured with, kept
                   ;; on the entry; nil (no bound) for a run that named none and for a
                   ;; swept firing (`record-swept-firing!`)
                   bound (:max-depth entry)]
               (drop-refusal! kb rh entry)
               (if (and bound (> depth (long bound)))
                 []
                 (vec (place-conclusion kb rule (:conseq entry) (:pctx entry)
                                        (:antes entry) depth (:bindings entry)
                                        (:strength rule) (:subsumptions entry)))))))

;; ---- a permuting mark leaving ---------------------------------------------
;; A mark that stops holding leaves rows spelled by it.  Each row keeps the spellings its
;; pieces were written in (`integrate/spellings-key`), and this puts every piece back at
;; the row its spelling canonicalizes to now: a premise assertion re-asserted at its own
;; class, a rule firing re-placed with its antecedents and bindings.  A row no piece stays
;; on is swept with what was drawn from it.  A mark that starts holding again by a relabel
;; folds the rows through `integrate/commute-predicate`.

(defn- reassert-premise
  "Assert `written` in `ctx` at `strength`, unchained and unsettled — the settle this runs
  inside settles it — and return its handle, or nil when the entry point refuses it.  A
  row new here takes `prov`, the provenance of the row the assertion was folded into, so
  it keeps the creation provenance the caller's assertion recorded."
  [kb written ctx strength prov]
  (try
    (binding [wiring/*defer-settle?* true]
      (wiring/assert-sentence kb written ctx
                              (cond-> {:strength strength :chain? false}
                                (and (seq prov) (nil? (kb/find-sentex-handle kb written ctx)))
                                (assoc :provenance prov))))
    (catch clojure.lang.ExceptionInfo e
      (trove/log! {:level :warn :id ::respell-refused
                   :msg   "a premise spelling could not be re-asserted; it stays folded"
                   :data  {:sentence written :context ctx :type (:type (ex-data e))}})
      nil)))

(def respell-informant
  "`jtms/respell-informant`, the informant `ensure-respellings!` justifies a spelling by."
  jtms/respell-informant)

(defn- piece-holder?
  "Does row `h` hold a piece of a fact: a premise assertion or a rule firing?  Every other
  justification restates a row it rests on (`integrate/rule-justification?`)."
  [kb h]
  (let [tms (reasoning/tms kb)]
    (boolean (or (jtms/premise? tms h)
                 (some #(special/firing-informant? kb (:informant (jtms/justification tms %)))
                       (jtms/supports tms h))))))

(defn- sync-respellings!
  "Bring the `respell` justifications resting on row `h` to `want`, `{[spelling context]
  [store alts]}`: each spelling is stored by `store`, a fn answering `[handle sentex
  new?]`, and justified `respell` by `[h & alt]` once for each `alt` of `alts`; a
  `respell` justification resting on `h` whose row and antecedents `want` does not name
  is dropped, or with `on-stale` none is and `(on-stale)` is called when one is owed.
  Returns the rows it created, for the agenda."
  ([kb h want] (sync-respellings! kb h want nil))
  ([kb h want on-stale]
   (let [tms   (reasoning/tms kb)
         recs  (:records kb)
         named (fn [j]
                 (when-let [c (p/get-sentex recs (:consequence j))]
                   (let [as (set (:antecedents j))]
                     (some #(= as (into #{h} (remove nil?) %))
                           (second (get want [(sx/sentence-of c) (:context c)]))))))
         stale (into [] (filter (fn [jid]
                                  (let [j (jtms/justification tms jid)]
                                    (and (= respell-informant (:informant j)) (not (named j))))))
                     (jtms/dependents tms h))]
     (if on-stale
       (when (seq stale) (on-stale))
       (doseq [jid stale]
         (let [r (jtms/drop-justification! tms jid)]
           (p/delete-justification! recs jid)
           (integrate/apply-removals! kb r))))
     (into []
           (mapcat
            (fn [[_ [store alts]]]
              (let [[h2 sx2 new?] (store)]
                (when new?
                  (checks/force-sentex! kb sx2)
                  (special/integrate-twin kb sx2 h2))
                (doseq [w alts :let [antes (into [h] (remove nil?) w)]]
                  (jtms/ensure-node tms h2 (inc (reduce max (map #(jtms/depth tms %) antes))))
                  (when-not (jtms/has-justification? tms respell-informant antes h2)
                    (let [just (jtms/->just (p/next-id recs) respell-informant antes h2 {} :monotonic)]
                      (p/put-justification recs just)
                      (jtms/add-justification tms just))))
                (when new? [h2]))))
           (sort-by (comp nm/print-key key) want)))))

(defn- ensure-respellings!
  "Bring the `respell` justifications resting on row `h` to the spellings the readers of
  its pieces read (`integrate/spelling-plan`, `sync-respellings!`): each is stored at
  `h`'s context, justified once for each set of marks that sorts `h`'s spelling into it
  (`inherit/permuted-read-supports`).  A row holding no piece of its own, or not at its
  pieces' home, gives no spelling.  Returns the rows it created, for the agenda."
  [kb planner h]
  (let [sx (p/get-sentex (:records kb) h)]
    (when (and sx (not (:antecedent sx)))
      (let [s          (:sentence sx)
            ctx        (:context sx)
            pred       (res/permuted-functor s)
            [home _ r] (integrate/spelling-plan kb planner s ctx)
            inner      #(if (= 'not (first %)) (second %) %)]
        (sync-respellings!
         kb h
         (into {}
               (map (fn [[s2 e]]
                      [[s2 ctx] [#(integrate/spelled pred ctx e (fn [] (kb/find-or-create-sentex kb s2 ctx)))
                                 (or (inherit/permuted-read-supports kb (inner s) (vec (rest (inner s2))) ctx)
                                     [[(integrate/mark-witness kb pred)]])]]))
               (when (and (= home s) (piece-holder? kb h)) r)))))))

(defn- split-row!
  "Put each piece of row `sx` whose spelling's home is not the row's own spelling at the
  row it is home at (`integrate/spelling-plan` of `(spell written)`), store the spellings
  the readers of each moved piece read beside it (`ensure-respellings!`), and only then
  take the piece off this row.  Returns the handles the moves created or re-premised, for
  the agenda."
  [kb planner sx spell]
  (let [tms      (reasoning/tms kb)
        recs     (:records kb)
        h        (:id sx)
        stored   (:sentence sx)
        ctx      (:context sx)
        pred     (res/permuted-functor stored)
        plan     (memoize #(integrate/spelling-plan kb planner (spell %) ctx))
        stays?   #(= stored (first (plan %)))
        at-home  (fn [w f] (let [[hw e] (plan w)] (integrate/spelled pred ctx e #(f hw))))
        prem     (integrate/premise-spellings kb h stored)
        supports (jtms/supports tms h)
        derived  (into {} (filter (comp #(contains? supports %) key))
                       (:derived (integrate/spellings kb h)))
        move-d   (into {} (remove (comp stays? val)) derived)
        ;; the premise assertions, in content order, re-asserted first: a spelling the
        ;; entry point refuses stays on this row rather than leaving belief behind
        moved-p  (into {}
                       (keep (fn [[w st]]
                               (when-not (stays? w)
                                 (when-let [h' (at-home w #(reassert-premise
                                                            kb % ctx st
                                                            (dissoc (p/get-provenance recs h)
                                                                    integrate/spellings-key)))]
                                   [w h']))))
                       (sort-by (comp nm/print-key key) prem))
        keep-p   (apply dissoc prem (keys moved-p))
        placed   (into []
                       (mapcat (fn [[jid w]]
                                 (let [j  (p/get-justification recs jid)
                                       rh (:informant j)]
                                   (when (and j (integer? rh) (p/get-sentex recs rh))
                                     (at-home w #(place-conclusion
                                                  kb (rule-fields kb rh) % ctx (conj (vec (:antecedents j)) rh)
                                                  (inc (reduce max 0 (map (fn [a] (jtms/depth tms a)) (:antecedents j))))
                                                  (:bindings j) (:strength j) (:subsumptions j)))))))
                       (sort-by (comp nm/print-key val) move-d))
        ;; a moved firing's antecedents are read again by the agenda: a fold may have
        ;; merged two firings that differ only in their bindings, and the one it kept
        ;; names the spelling the mark's leaving moves away from the row it rests on
        reread   (into [] (comp (keep #(p/get-justification recs %)) (mapcat :antecedents))
                       (keys move-d))
        homes    (into (set (vals moved-p))
                       (keep #(at-home % (fn [hw] (kb/find-sentex-handle kb hw ctx))))
                       (vals move-d))
        twins    (into [] (mapcat #(ensure-respellings! kb planner %)) (sort homes))]
    ;; ...and only then off this row, so nothing drawn from the proposition is swept
    ;; while its new row is still being written
    (doseq [jid (keys move-d)]
      (let [r (jtms/drop-justification! tms jid)]
        (p/delete-justification! recs jid)
        (integrate/apply-removals! kb r)))
    (when (seq moved-p)
      (if (seq keep-p)
        (let [st (reduce strength/max nil (vals keep-p))]
          (jtms/add-premise tms h st)
          (p/mark-premise recs h st))
        (do (p/unmark-premise! recs h)
            (integrate/apply-removals! kb (jtms/retract! tms h)))))
    (when (p/get-sentex recs h)
      (integrate/put-spellings!
       kb h (integrate/normalized-spellings stored {:premise keep-p
                                                    :derived (apply dissoc derived (keys move-d))})))
    (-> (vec (vals moved-p)) (into placed) (into twins)
        (into (filter #(p/get-sentex recs %)) reread))))

(defn- permuting-witness
  "A believed statement of a permuting mark that spells `sentence` (`integrate/mark-witness`):
  its literal's predicate's first, then the first by name among the functors of the
  compounds below it.  Nil when no mark permutes it."
  [kb sentence]
  (when (and sentence (integrate/permuting-sentence? kb sentence))
    (let [top (res/permuted-functor sentence)
          fs  (sx/compound-functors (if (= 'not (first sentence)) (second sentence) sentence)
                                    (res/opaque-fn (reasoning/taxonomy kb)))]
      (some #(when (integrate/permuting? kb %) (integrate/mark-witness kb %))
            (cons top (sort-by nm/print-key (disj fs top)))))))

(defn- respell-rows!
  "Bring the stored rows `hs` to the spellings their readers read: split each
  (`split-row!`), fold each into the row its spelling is home at
  (`integrate/commute-predicate`'s walk, once per row), then store the spellings each
  row's readers read beside it (`ensure-respellings!`).  Returns the handles that are new
  content, for the agenda."
  [kb hs]
  (let [recs    (:records kb)
        planner (res/spelling-planner kb)
        split   (into [] (mapcat #(when-let [sx (p/get-sentex recs %)]
                                    (split-row! kb planner sx
                                                (fn [w] (if (nat/permutes-reified? kb w)
                                                          (nat/maybe-reify-nats kb w false (:context sx))
                                                          w)))))
                      hs)
        folded  (into [] (keep (fn [h]
                                 (when-let [sx (p/get-sentex recs h)]
                                   (when-let [w (permuting-witness kb (:sentence sx))]
                                     (integrate/fold-row-home! kb planner sx w)))))
                      hs)
        rows    (into (sorted-set) (filter #(p/get-sentex recs %))
                      (concat hs split (map :at folded)))]
    (-> split (into (mapcat :new) folded) (into (mapcat #(ensure-respellings! kb planner %)) rows))))

(defn reconcile-spellings!
  "Bring the stored rows of every predicate in `preds` (`integrate/rows-spelled-by`) — the ones whose permuting marks
  moved since the last settle (`special/note-permuting-moves!`), or whose marks a placed
  `defeat` or an `except` moved at some reader (`special/note-mark-reach!`) — and the rows
  `rows` a write stored while its predicate's readers disagree, to the spellings their
  readers read (`respell-rows!`), and return the handles that are new content, for the
  agenda.  Linear in the moved predicates' stored rows, with a provenance read per row: a
  mark moving is a declaration reaching its facts, and `commute-existing` pays the same
  on arrival."
  ([kb preds] (reconcile-spellings! kb preds nil))
  ([kb preds rows]
   (let [idx (:index kb)]
     (into (respell-rows! kb (sort rows))
           (mapcat (fn [pred]
                     (when-let [hs (not-empty (integrate/rows-spelled-by idx pred))]
                       (respell-rows! kb hs))))
           (sort-by nm/print-key preds)))))

(defn- respelling
  "The spelling the write path gives stored row `sx` now (`nat/respelled`), canonical in
  its context, or nil when that is its spelling already.  A mint the respelling owes and
  the entry point refuses leaves the row as it is, logged, as a refused premise spelling
  is (`reassert-premise`)."
  [kb sx]
  (try
    (let [s    (sx/sentence-of sx)
          want (kb/canonical-sentence kb (nat/respelled kb s (:context sx)) (:context sx))]
      (when (not= want s) want))
    (catch clojure.lang.ExceptionInfo e
      (when-not (:type (ex-data e)) (throw e))
      (trove/log! {:level :warn :id ::reify-refused
                   :msg   "a reified spelling could not be minted; the row keeps its spelling"
                   :data  {:sentence (sx/sentence-of sx) :context (:context sx) :type (:type (ex-data e))}})
      nil)))

(defn- collect-respelled-orphans!
  "Take out the bookkeeping of every reified constant that `departed`, the spellings a
  re-spell moved rows off, named and no use names now (`nat/orphans-named-by`), looping
  while a removal orphans a constant its expression named.  `nat-maintenance`'s orphan
  sweep, for a settle, which has no teardown entry point to retract through: each handle
  goes through `integrate/take-out!`, and the removals reach a teardown's removal record
  when one is bound."
  [kb departed]
  (let [recs (:records kb)]
    (loop [region departed guard 0]
      (let [hs (into [] (comp (mapcat #(nat/bookkeeping-handles kb %)) (distinct))
                     (nat/orphans-named-by kb region))]
        (when (and (seq hs) (< guard 64))
          (let [sink (volatile! [])]
            (binding [integrate/*removed-sink* sink]
              (doseq [h hs :when (p/get-sentex recs h)] (integrate/take-out! kb h)))
            (when-let [outer integrate/*removed-sink*] (vswap! outer into @sink))
            (recur @sink (inc guard))))))))

(defn- reified-fns
  "The `reifiable_function` functions some reader does not believe the mark of whose
  applications `s` holds, written or as a constant minted for one, sorted.

  The mark is read unscoped, a superset that `nat-read/split-reifiable?` narrows to the
  functions some reader does not believe the mark of."
  [kb s]
  (let [tax (reasoning/taxonomy kb)]
    (->> (tree-seq sequential? seq (nat/expand-expression kb s nat-read/reified-object-symbol?))
         (keep #(when (and (sequential? %) (seq %)) (first %)))
         (filter #(and (symbol? %) (tax/has-prop? tax :reifiable %)))
         distinct
         (filter #(nat-read/split-reifiable? kb %))
         sort
         vec)))

(defn- written-rule?
  "Does row `h` hold a rule whose premise assertions record a written spelling: one an
  open application's respell stored under its corresponding predicate?"
  [kb h]
  (boolean (seq (:premise (integrate/spellings kb h)))))

;; ---- the correspondence derivations of a minted constant -----------------------
;; docs/nat.md, The corresponding predicate.  A projection, a merge onto a `:monotonic`
;; value and a copy onto a `:default` one are derivations under the declaration.

(def correspondence-informant
  "The informant a correspondence derivation of a fact is justified under."
  res/correspondence-predicate)

(def ^:private correspondence-rule
  "The rule map `place-fact-conclusion` places a correspondence derivation under: the
  engine informant and no rule handle."
  {:name correspondence-informant :rule-handle nil})

(defn- stored-declarations
  "`[handle context predicate position]` for each stored correspondence declaration of
  function `f` applied to `m` arguments, in handle order."
  [kb f m]
  (let [recs (:records kb)]
    (into []
          (keep (fn [h]
                  (when-let [{s :sentence c :context} (p/get-sentex recs h)]
                    (let [[_ f' pr n] s
                          pos         (if (integer? n) n (inc m))]
                      (when (and (= f f') (symbol? pr) (<= 3 (count s) 4) (<= 1 pos (inc m)))
                        [h c pr pos])))))
          (sort (reads/as-stored-with-args (:index kb) res/correspondence-predicate {1 f})))))

(defn- restated?
  "Is stored row `h` a merge's restatement alone: not a premise, and every justification
  under an equality relation (`kb/equality-predicates`)?"
  [kb h]
  (let [tms (reasoning/tms kb)
        js  (keep #(jtms/justification tms %) (jtms/supports tms h))]
    (and (not (jtms/premise? tms h)) (seq js)
         (every? #(contains? kb/equality-predicates (:informant %)) js))))

(defn- value-entries
  "`{:value :fact :fctx :decl :dctx}` for each stored fact naming a value for the
  application `E` under a stored declaration of its function: a symbol at the declared
  position that is not a reified constant, on a row that is not a merge's restatement."
  [kb E]
  (let [recs (:records kb)
        args (vec (rest E))
        m    (count args)]
    (for [[d dctx pr pos] (stored-declarations kb (first E) m)
          :let  [probe (into {} (keep-indexed (fn [i a]
                                                (when (sx/indexable-term? a)
                                                  [(if (< i (dec pos)) (inc i) (+ i 2)) a])))
                             args)]
          h     (sort (reads/as-stored-with-args (:index kb) pr probe))
          :let  [{s :sentence c :context} (p/get-sentex recs h)
                 vs (vec (rest s))]
          :when (and (= pr (first s)) (= (inc m) (count vs))
                     (= args (into (subvec vs 0 (dec pos)) (subvec vs pos))))
          :let  [v (nth vs (dec pos))]
          :when (and (symbol? v) (not (nm/reified-constant? v)) (not (restated? kb h)))]
      {:value v :fact h :fctx c :decl d :dctx dctx :pred pr :pos pos})))

(defn- sole-value-at?
  "Does `ctx` read `E`'s function through the one correspondence `[pr pos]`
  (`res/correspondence-of`), and do the corresponding facts visible from `ctx` name no
  value for `E` outside the classes of `v` and the constant `k`
  (`res/corresponding-values`)?"
  [kb E k v pr pos ctx]
  (and (= [pr pos] (res/correspondence-of kb (first E) (count (rest E)) ctx))
       (let [visible? (res/visible-supporter-fn kb ctx)]
         (empty? (disj (set (keys (res/corresponding-values kb E ctx)))
                       (res/normal-form kb v visible?) (res/normal-form kb k visible?))))))

(defn- valued-constants
  "`{k [E value-entries]}` for each reified object constant `form` names whose believed
  map gives it an application with a value fact (`value-entries`)."
  [kb form]
  (into {}
        (keep (fn [k]
                (when-let [E (res/minted-expression kb k)]
                  (when-let [vs (seq (value-entries kb E))] [k [E vs]]))))
        (distinct (filter nat-read/reified-object-symbol? (tree-seq sequential? seq form)))))

(defn- copy-want
  "`sync-respellings!`'s want for the copies of rule row `sx` onto the `:default` values
  of the constants it names (docs/nat.md, The corresponding predicate): the rule with
  each such constant `k` replaced by its value `v`, stored at each maximal context that
  sees the rule's context, the value's fact and the declaration where that is the one
  value outside `k`'s class, and justified by the fact and the declaration.  Nil when
  the rule names no reified object constant or the KB declares no correspondence."
  [kb sx]
  (when (and (res/any-corresponding-predicates? kb)
             (some nat-read/reified-object-symbol? (tree-seq sequential? seq (sx/sentence-of sx))))
    (let [h   (:id sx)
          ctx (:context sx)
          tms (reasoning/tms kb)
          s   (sx/sentence-of sx)]
      (reduce
       (fn [acc [k [E vs]]]
         (reduce
          (fn [acc {:keys [value fact fctx decl dctx pred pos]}]
            (let [s2 (rules/rewrap-sentex (walk/postwalk-replace {k value} s) sx)]
              (reduce (fn [acc c]
                        (if (sole-value-at? kb E k value pred pos c)
                          (update acc [(kb/canonical-sentence kb s2 c) c]
                                  (fn [[st as]] [(or st #(kb/find-or-create-sentex kb s2 c))
                                                 (conj (or as []) [fact decl])]))
                          acc))
                      acc
                      (sort-by nm/name-key
                               (res/exception-aware-placements
                                kb (cond->> [fact decl] (not (jtms/forced? tms :held h)) (cons h))
                                [ctx fctx dctx])))))
          acc vs))
       {}
       (sort-by (comp nm/name-key key) (valued-constants kb s))))))

(defn- correspondence-want
  "`sync-respellings!`'s want for rule row `sx`: each spelling its written spellings `ws`
  read through the believed correspondences of every context (`res/rule-respellings`),
  wrapped as `sx` is.  A spelling reading the declarations `ds` is stored at each maximal
  context that sees `sx`'s context and every one of `ds` (`res/exception-aware-placements`)
  and justified by `ds`; a spelling with no such context is stored nowhere.  The row's own
  spelling at its own context is left out."
  [kb sx ws]
  (let [ctx  (:context sx)
        h    (:id sx)
        tms  (reasoning/tms kb)
        recs (:records kb)
        at   (fn [ds]
               (let [ds (remove nil? ds)]
                 (res/exception-aware-placements
                  kb (cond->> ds (not (jtms/forced? tms :held h)) (cons h))
                  (into [ctx] (keep #(:context (p/get-sentex recs %))) ds))))
        put  (fn [acc s ds c]
               (update acc [(kb/canonical-sentence kb s c) c]
                       (fn [[st as]] [(or st #(kb/find-or-create-sentex kb s c)) (conj (or as []) ds)])))]
    (dissoc (reduce (fn [acc [s alts]]
                      (reduce (fn [acc ds] (reduce #(put %1 s ds %2) acc (sort-by nm/name-key (at ds))))
                              acc alts))
                    {}
                    (mapcat #(res/rule-respellings kb (rules/rewrap-sentex % sx) nil)
                            (sort-by nm/print-key ws)))
            [(sx/sentence-of sx) ctx])))

(defn- rule-correspondence-want
  "`correspondence-want` for stored rule row `sx` over its written spellings, or over its
  own spelling when it records none and holds an open application
  (`nat/held-application?`), with the copies onto the `:default` values of the constants
  it names (`copy-want`); nil for any other row."
  [kb sx]
  (when (some? (:antecedent sx))
    (let [h      (:id sx)
          copies (copy-want kb sx)
          want   (cond
                   (written-rule? kb h)
                   (correspondence-want kb sx (keys (integrate/premise-spellings kb h (sx/sentence-of sx))))
                   (nat/held-application? kb sx)
                   (correspondence-want kb sx [(sx/sentence-of sx)]))]
      (if copies
        (merge-with (fn [[st as] [_ as2]] [st (into as as2)]) (or want {}) copies)
        want))))

(defn- reified-plan
  "`[home withheld respelled]` for stored row `s` in `ctx`, `integrate/spelling-plan`'s
  answer for a `reifiable_function` mark: `home`, the spelling the row's pieces sit at,
  spelled with the functions `withheld` left as written, and `respelled`,
  `{spelling withheld}` for every other spelling a reader reads.  Every reader believing
  every mark it names reads the write path's spelling (`respelling`, `withheld` nil);
  readers that disagree leave the row as written at home.  `memo` holds each
  `[functions context]`'s readers for one reconcile."
  [kb memo s ctx]
  (let [fs (reified-fns kb s)]
    (if (empty? fs)
      [(or (respelling kb {:sentence s :context ctx}) s) nil {}]
      (let [ents  (into {} (map #(first (nat-read/reifiable-entries kb %))) fs)
            rdrs  (or (get @memo [fs ctx])
                      (let [v (into [] (comp (map #(res/entries-at kb ents %)) (distinct))
                                    (res/spelling-readers kb ctx (into [] (mapcat (comp keys val)) ents)))]
                        (vswap! memo assoc [fs ctx] v)
                        v))
            spell (fn [w] (binding [nat-read/*withheld* w]
                            (kb/canonical-sentence kb (nat/respelled kb s ctx) ctx)))
            sp    (into {} (map (fn [b] (let [w (reduce disj (set fs) (map #(nth % 2) b))]
                                          [(spell w) w])))
                        rdrs)]
        (if (= 1 (count sp))
          (let [[s1 w] (first sp)] [s1 w {}])
          (let [u (spell (set fs))] [u (set fs) (dissoc sp u)]))))))

(defn- reconcile-row-spelling!
  "`reconcile-reified-row!`'s arm for a row recording no written rule spelling:
  `[handle new]`, the handle the row ends at and the handles that are new content, or
  nil when `h` holds no piece."
  [kb memo moved witness pre h]
  (let [tax (reasoning/taxonomy kb)
        tms (reasoning/tms kb)]
    (when-let [sx (p/get-sentex (:records kb) h)]
      (when (piece-holder? kb h)
        (let [s          (sx/sentence-of sx)
              ctx        (:context sx)
              s'         (pre s)
              [home w r] (reified-plan kb memo s' ctx)
              h'         (when (not= home s)
                           (vswap! moved conj sx)
                           (let [kept (into (or w #{}) (nat/permuted-reifiable-functions kb))]
                             (binding [nat-read/*withheld* (or w #{})]
                               (integrate/move-row!
                                kb sx home witness
                                #(binding [nat-read/*withheld* kept]
                                   (nat/respelled kb (pre %) ctx))))))
              at         (or (:at h') h)
              sx'        (when (some? (:antecedent sx)) (p/get-sentex (:records kb) at))]
          [at
           (cond-> (sync-respellings!
                    kb at
                    (into (or (some->> sx' (rule-correspondence-want kb)) {})
                          (map (fn [[s2 w2]]
                                 [[s2 ctx] [#(binding [nat-read/*withheld* w2]
                                               (kb/find-or-create-sentex kb s2 ctx))
                                            (into [] (comp (filter (fn [m] (jtms/in? tms m)))
                                                           (map vector))
                                                  (sort (mapcat (fn [g] (tax/prop-supporters tax :reifiable g))
                                                                (remove w2 (reified-fns kb s')))))]]))
                          r))
             h' (into (:new h')))])))))

(defn- reconcile-recorded-fact!
  "`reconcile-reified-row!`'s arm for fact row `sx` some piece of which records a written
  spelling whose home (`reified-plan`) is not the home of the row's own spelling: each
  piece goes to its home (`split-row!`), the row is added to `moved`, and the row left
  holding a piece goes on to `reconcile-row-spelling!`.  Returns `[handle new]` as that arm
  does, or nil when no recorded home differs, for that arm alone."
  [kb memo moved witness pre sx]
  (when (and sx (nil? (:antecedent sx)))
    (let [h    (:id sx)
          ctx  (:context sx)
          rec  (integrate/spellings kb h)
          sup  (jtms/supports (reasoning/tms kb) h)
          ws   (concat (keys (:premise rec)) (keep (fn [[jid w]] (when (contains? sup jid) w)) (:derived rec)))
          home (memoize #(first (reified-plan kb memo (pre %) ctx)))
          own  (home (:sentence sx))]
      (when (some #(not= own (home %)) ws)
        (vswap! moved conj sx)
        (let [new       (split-row! kb (res/spelling-planner kb) sx home)
              [at new2] (reconcile-row-spelling! kb memo moved witness pre h)]
          [at (into (vec new) new2)])))))

(defn sync-rule-respellings!
  "Store every other spelling that rule row `h`'s written spellings read through the
  believed correspondences, each justified `respell` by `h` and the declarations it reads
  at the contexts that see both (`correspondence-want`, docs/nat.md, The corresponding
  predicate), and drop the ones no longer read.  A row recording no written spelling and
  holding no open application (`nat/held-application?`) is left alone.  Returns the rows
  it created, for the agenda.  `on-stale` is `sync-respellings!`'s."
  ([kb h] (sync-rule-respellings! kb h nil))
  ([kb h on-stale]
   (when-let [want (some->> (p/get-sentex (:records kb) h) (rule-correspondence-want kb))]
     (sync-respellings! kb h want on-stale))))

(defn sync-held-respellings!
  "Store the spellings each rule in the `:held` forced set reads at the contexts it meets a
  correspondence declaration in (`sync-rule-respellings!`), and answer the rows it
  created: `recover`'s pass, for a store written before a held rule stored them.  Linear
  in the `:held` set; one functor count on a KB declaring no correspondence."
  [kb]
  (when (res/any-corresponding-predicates? kb)
    (into [] (mapcat #(sync-rule-respellings! kb %))
          (sort (jtms/forced-members (reasoning/tms kb) :held)))))

(defn- reconcile-written-rule!
  "Bring rule row `sx`, whose premise assertions record their written spellings, to the
  spelling each one is stored at now (`reified-plan` of the spelling as written): the
  pieces whose spelling is not the one the row keeps are re-asserted at theirs with the
  row's wrappers (`reassert-premise`, `rules/rewrap-sentex`) and taken off the row.  The
  row keeps its own spelling's pieces, or the content-least spelling's, and moves there.
  Returns `[handle new]` as `reconcile-row-spelling!` does.  A row moved off its spelling
  is added to `moved`."
  [kb memo moved witness pre sx]
  (let [tms    (reasoning/tms kb)
        recs   (:records kb)
        h      (:id sx)
        s      (sx/sentence-of sx)
        ctx    (:context sx)
        prem   (integrate/premise-spellings kb h s)
        groups (group-by #(first (reified-plan kb memo (pre (key %)) ctx)) prem)
        stay   (if (contains? groups s) s (first (sort-by nm/print-key (keys groups))))
        prov   (dissoc (p/get-provenance recs h) integrate/spellings-key)
        out    (into [] (comp (mapcat val)
                              (keep (fn [[w st]]
                                      (reassert-premise kb (rules/rewrap-sentex w sx) ctx st prov))))
                     (sort-by (comp nm/print-key key) (dissoc groups stay)))]
    (when (< 1 (count groups))
      (let [keep-p (into {} (get groups stay))
            st     (reduce strength/max nil (vals keep-p))]
        (jtms/add-premise tms h st)
        (p/mark-premise recs h st)
        (integrate/put-spellings! kb h (integrate/normalized-spellings
                                        s (assoc (integrate/spellings kb h) :premise keep-p)))))
    ;; the spellings beside the row first, so none of them is the spelling the row moves to
    (let [ws   (keys (integrate/premise-spellings kb h s))
          pre1 (sync-respellings! kb h (dissoc (correspondence-want kb sx ws) [stay ctx]))
          m    (when (not= stay s)
                 (vswap! moved conj sx)
                 (integrate/move-row! kb (p/get-sentex recs h) stay witness #(nat/respelled kb (pre %) ctx)))
          at   (or (:at m) h)
          post (some-> (p/get-sentex recs at) (#(sync-respellings! kb at (correspondence-want kb % ws))))]
      [at (into [] (filter #(p/get-sentex recs %)) (concat out (:new m) pre1 post))])))

(defn- reconcile-reified-row!
  "Bring stored row `h` to the spellings its readers read, planned from `(pre sentence)`,
  and return the handles that are new content.  `pre` is `identity`, or for a use a departed
  map left behind, `nat/written-as` over the departed maps (`reconcile-stranded!`).  A row moved
  off its spelling is added to `moved`; `witness` is the mark handle a fold carries metas on,
  or nil; `memo` is `reified-plan`'s.  A rule row is forced again afterwards
  (`checks/force-sentex!`).  When a rule's antecedents or `:out` / `:held` membership moved,
  the firings it made under the spelling it left are dropped, the rows they swept are added to
  `moved`, and a rule that ends believed is returned so the agenda fires it again; a rule whose
  consequent names an open application is treated the same way.  With `redecide?`, the `:out`
  membership may have moved before the call (`reconcile-formula-positions!`), so a rule that
  ends held keeps no firing; without it, a rule held by an open application
  (`nat/held-application?`) keeps none either."
  ([kb memo moved witness pre h] (reconcile-reified-row! kb memo moved witness pre h false))
  ([kb memo moved witness pre h redecide?]
   (let [recs  (:records kb)
         tms   (reasoning/tms kb)
         out?  #(or (jtms/forced? tms :out %) (jtms/forced? tms :held %))
         held  (out? h)
         antes (:antecedent (p/get-sentex recs h))
         [at new] (if (and (some? antes) (written-rule? kb h) (piece-holder? kb h))
                    (reconcile-written-rule! kb memo moved witness pre (p/get-sentex recs h))
                    (or (reconcile-recorded-fact! kb memo moved witness pre (p/get-sentex recs h))
                        (reconcile-row-spelling! kb memo moved witness pre h)))
         sx    (some->> at (p/get-sentex recs))
         drop! (fn []
                 ;; the drops it filed go with its firings; a firing made again files its own
                 (violations/withdraw-rule! kb at)
                 (doseq [jid (into (sorted-set)
                                   (filter (fn [jid] (= at (:informant (jtms/justification tms jid)))))
                                   (jtms/dependents tms at))
                         :when (jtms/justification tms jid)]
                   (let [r (jtms/drop-justification! tms jid)]
                     ;; a swept conclusion's constants are orphan candidates, as a moved row's are
                     (vswap! moved into (keep (fn [d] (p/get-sentex recs d))) (:removed-sentexes r))
                     (p/delete-justification! recs jid)
                     (integrate/apply-removals! kb r))))]
     (if (some? (:antecedent sx))
       (do (checks/force-sentex! kb sx)
           (cond
             ;; a consequent naming an open application fires again: its firings minted
             ;; under the marks and correspondences that held when they were placed
             (or (not (and (= antes (:antecedent sx)) (= held (out? at))))
                 (nat/names-open-application? kb (:consequent sx)))
             (do (drop!) (cond-> (vec new) (not (out? at)) (conj at)))
             (if redecide? (out? at) (nat/held-application? kb sx)) (do (drop!) new)
             :else new))
       new))))

(defn- mark-witness
  "The believed supporter of `f`'s `reifiable_function` mark chosen by content, or nil."
  [kb f]
  (integrate/witness-among kb (tax/prop-supporters (reasoning/taxonomy kb) :reifiable f)))

(defn- reconcile-regions!
  "Reconcile the rows `region-of` answers for each function of `fns`
  (`reconcile-reified-row!`, content order), collect the orphans the moved rows leave, and
  return the handles that are new content."
  [kb fns region-of]
  (let [moved (volatile! [])
        memo  (volatile! {})
        new   (binding [wiring/*defer-settle?* true]
                (into []
                      (mapcat
                       (fn [f]
                         (let [witness (mark-witness kb f)]
                           (into []
                                 (mapcat #(reconcile-reified-row! kb memo moved witness identity %))
                                 (distinct
                                  (map :id (nm/sort-by-content-key
                                            #(vector (sx/sentence-of %) (:context %)) (region-of f))))))))
                      (sort fns)))]
    (collect-respelled-orphans! kb @moved)
    new))

(defn reconcile-reified!
  "Bring the stored rows a `reifiable_function` mark moving re-spells to the spellings
  their readers read, for every function in `fns` — the ones whose mark moved since the
  last settle (`special/note-permuting-moves!`), or whose readers came to disagree
  (`nat/queue-split-uses!`, `special/note-mark-reach!`) — and return the handles that are
  new content, for the agenda (docs/nat.md, A reifiable mark moving).  The region of each
  function also holds the rules a correspondence of it respelled
  (`nat/corresponded-rules`), over the predicates of its stored declarations and
  `preds`, the predicates of declarations that left.  Linear in the regions read."
  ([kb fns] (reconcile-reified! kb fns nil))
  ([kb fns preds]
   (reconcile-regions! kb fns
                       (fn [f] (into (vec (nat/respell-region kb f))
                                     (nat/corresponded-rules kb f preds #(written-rule? kb %)))))))

(defn reconcile-corresponded!
  "Bring the rules a `genlCx` move can re-spell through a correspondence of each function
  of `fns` (`special/note-moved-correspondences!`) to the declarations their contexts and
  the contexts below them see, and return the handles that are new content: the rules the
  `:held` forced set holds that apply the function, and the rules a correspondence of it
  respelled (`nat/corresponded-rules`).  Linear in those rules and the `:held` set; reads
  no fact and no constant (docs/nat.md, The corresponding predicate)."
  [kb fns]
  (let [recs (:records kb)
        held (delay (into [] (keep #(p/get-sentex recs %))
                          (sort (jtms/forced-members (reasoning/tms kb) :held))))]
    (reconcile-regions! kb fns
                        (fn [f] (into (filterv #(nat/applies? f (sx/sentence-of %)) @held)
                                      (nat/corresponded-rules kb f nil #(written-rule? kb %)))))))

(defn- rewrite-entries
  "`[handle context target]` for each stored compound `(rewriteOf T E)` naming the
  expression `E`, in handle order."
  [kb E]
  (into []
        (keep (fn [h]
                (let [{s :sentence c :context} (p/get-sentex (:records kb) h)]
                  (when (and (= 'rewriteOf (first s)) (= E (nth s 2 nil)) (symbol? (second s)))
                    [h c (second s)]))))
        (sort (reads/as-stored-with-args (:index kb) 'rewriteOf {2 E}))))

(defn- value-want
  "`{[sentence context] {antecedent-set [kind antecedents]}}`: what constant `k` mapped to
  `E` by its maps `mhs` owes under the stored declarations of `E`'s function, `kind` `:fact` or
  `:merge`.  A projection `(P … k …)` per declaration at each maximal common descendant of
  CxUniverse and the declaration's context; per value fact (`value-entries`), at each placement
  where that value is the one outside `k`'s class (`sole-value-at?`), the merge `(rewriteOf v
  k)` when the fact is `:monotonic` (`tuple/monotonic-member?`) and a copy of each fact `uses`
  holds with `v` in `k`'s place; per compound `(rewriteOf T E)` (`rewrite-entries`) and use, the
  merge `(rewriteOf T k)` at each placement where `T` is the target
  (`nat-read/rewrite-target`)."
  [kb k E mhs uses]
  (let [tms  (reasoning/tms kb)
        args (rest E)
        add  (fn [acc s c antes kind]
               (assoc-in acc [[(kb/canonical-sentence kb s c) c] (set antes)] [kind antes]))
        at   (fn [hs cs] (sort-by nm/name-key (res/exception-aware-placements kb hs cs)))]
    (as-> {} acc
      (reduce (fn [acc [d dctx pr pos]]
                (reduce (fn [acc mh]
                          (reduce #(add %1 (apply list pr (res/insert-at args pos k)) %2 [mh d] :fact)
                                  acc (at [mh d] [sx/root-context dctx])))
                        acc mhs))
              acc (stored-declarations kb (first E) (count args)))
      (reduce (fn [acc {:keys [value fact fctx decl dctx pred pos]}]
                (let [acc (if (tuple/monotonic-member? tms fact)
                            (reduce #(if (sole-value-at? kb E k value pred pos %2)
                                       (add %1 (list 'rewriteOf value k) %2 [fact decl] :merge)
                                       %1)
                                    acc (at [fact decl] [fctx dctx]))
                            acc)]
                  (reduce (fn [acc u]
                            (let [s2 (walk/postwalk-replace {k value} (sx/sentence-of u))]
                              (reduce #(if (sole-value-at? kb E k value pred pos %2)
                                         (add %1 s2 %2 [(:id u) fact decl] :fact)
                                         %1)
                                      acc (at [(:id u) fact decl] [(:context u) fctx dctx]))))
                          acc uses)))
              acc (value-entries kb E))
      (reduce (fn [acc [rh rctx t]]
                (reduce (fn [acc u]
                          (reduce #(if (= (res/normal-form kb t (res/visible-supporter-fn kb %2))
                                          (nat-read/rewrite-target kb E nat-read/nat-namespace %2))
                                     (add %1 (list 'rewriteOf t k) %2 [rh (:id u)] :merge)
                                     %1)
                                  acc (at [rh (:id u)] [rctx (:context u)])))
                        acc uses))
              acc (rewrite-entries kb E)))))

(defn- owned-justifications
  "The `correspondence-informant` justifications constant `k`'s value maintenance owns,
  as ids: on the projections resting on its maps `mhs`, on the merges `(rewriteOf v k)`
  among `named` (the rows naming `k`), and on the copies resting on a use of `uses`
  whose conclusion names no `k`."
  [kb k mhs named uses]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        mine (fn [jid] (= correspondence-informant (:informant (jtms/justification tms jid))))]
    (into (sorted-set)
          (concat (filter mine (mapcat #(jtms/dependents tms %) mhs))
                  (filter mine (mapcat #(jtms/supports tms (:id %))
                                       (filter #(let [s (:sentence %)]
                                                  (and (= 'rewriteOf (nm/functor s)) (= k (nth s 2 nil))))
                                               named)))
                  (filter #(and (mine %)
                                (not (some-> (p/get-sentex recs (:consequence (jtms/justification tms %)))
                                             sx/sentence-of
                                             (->> (tree-seq sequential? seq) (some #{k})))))
                          (mapcat #(jtms/dependents tms (:id %)) uses))))))

(defn- place-merge!
  "Store the merge `sentence` in `ctx` from `antes` (`special/derive-merge`), apply the
  supersessions it starts and file its violations, and return the handles that are new
  content."
  [kb sentence ctx antes]
  (let [new? (nil? (kb/find-sentex-handle kb sentence ctx))
        mig  (special/derive-merge kb sentence ctx correspondence-informant antes)]
    (when (seq (:superseded mig)) (special/refresh-supersessions kb (:superseded mig)))
    (when (seq (:violations mig)) (violations/report kb (:violations mig)))
    (cond-> (vec (:new mig))
      new? (conj (kb/find-sentex-handle kb sentence ctx)))))

(defn- sync-value!
  "Bring the correspondence derivations of reified object constant `k` to `value-want`:
  each wanted projection, merge and copy is placed, a projection or copy as a firing is
  (`place-fact-conclusion`), and each owned justification the want does not name is
  dropped, its conclusion going with its last support.  The rules naming `k` take their
  copies through `sync-rule-respellings!`.  With `deferred`, a volatile set, nothing is
  dropped, and `k` is added to `deferred` when a drop is owed.  Returns the handles that
  are new content."
  [kb k deferred]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        named (vec (kb/find-sentexes kb k))
        mhs   (into [] (comp (filter #(let [s (:sentence %)]
                                        (and (= sx/root-context (:context %)) (= 'natFormula (nm/functor s))
                                             (= k (second s)) (jtms/in? tms (:id %)))))
                             (map :id))
                    named)
        E     (res/minted-expression kb k)
        own?  (if E (nat/own-sentex-test kb k E named) (constantly true))
        uses  (into [] (remove #(or (some? (:antecedent %)) (own? %)
                                    (= 'natFormula (nm/functor (:sentence %)))
                                    (kb/equality-sentence? (:sentence %))))
                    named)
        want  (if E (value-want kb k E mhs uses) {})
        wanted? (fn [jid]
                  (let [j (jtms/justification tms jid)
                        c (p/get-sentex recs (:consequence j))]
                    (and c (contains? (get want [(sx/sentence-of c) (:context c)]) (set (:antecedents j))))))
        stale (filterv #(and (jtms/justification tms %) (not (wanted? %)))
                       (owned-justifications kb k mhs named uses))]
    (if deferred
      (when (seq stale) (vswap! deferred conj k))
      (doseq [jid stale :when (jtms/justification tms jid)]
        (let [r (jtms/drop-justification! tms jid)]
          (p/delete-justification! recs jid)
          (integrate/apply-removals! kb r))))
    (into []
          (concat
           (mapcat (fn [[[s c] by-antes]]
                     (mapcat (fn [[_ [kind antes]]]
                               (let [h (kb/find-sentex-handle kb s c)]
                                 (when-not (and h (jtms/has-justification? tms correspondence-informant antes h))
                                   (if (= :merge kind)
                                     (place-merge! kb s c antes)
                                     (let [hs (place-fact-conclusion kb correspondence-rule s c antes
                                                                     (inc (reduce max 0 (map #(jtms/depth tms %) antes)))
                                                                     {} :monotonic nil nil)
                                           ;; a new row spelled at a term a merge displaces is
                                           ;; restated, as an asserted one is
                                           r  (when-not h
                                                (some->> (kb/find-sentex-handle kb s c) (p/get-sentex recs)
                                                         (special/restate-retired kb)))]
                                       (when (seq (:violations r)) (violations/report kb (:violations r)))
                                       (into (vec hs) (:new r)))))))
                             (sort-by (comp nm/print-key key) by-antes)))
                   (sort-by (comp nm/print-key key) want))
           (mapcat #(sync-rule-respellings! kb (:id %) (when deferred (fn [] (vswap! deferred conj k))))
                   (filter #(some? (:antecedent %)) named))))))

(defn sync-values!
  "Bring the correspondence derivations of the constants `ks`, of every constant minted
  for a function of `fns`, and of the constants of a function of `fact-fns` a stored
  fact names a value of, to what the declarations, the facts and the uses stored now
  owe (`sync-value!`, docs/nat.md, The corresponding predicate), and return the handles
  that are new content, for the agenda.  The constants of `fact-fns` are read off the
  smaller side, the function's constants or its predicates' facts.  With `deferred`, a
  volatile set, nothing is dropped, and each constant owing a drop is added to it.  Linear
  in the uses of the constants it reads."
  ([kb ks fns fact-fns] (sync-values! kb ks fns fact-fns nil))
  ([kb ks fns fact-fns deferred]
   (when (or (seq ks) (seq fns) (seq fact-fns))
     (let [of-fn (fn [f] (map second (nat/minted-applications kb f)))
           valued (fn [f]
                    (let [preds (into #{} (comp (keep #(p/get-sentex (:records kb) %))
                                                (map #(nth (:sentence %) 2 nil))
                                                (filter symbol?))
                                      (reads/as-stored-with-args (:index kb) res/correspondence-predicate {1 f}))
                          nfacts (transduce (map #(reads/stored-count-with-functor (:index kb) %)) + preds)
                          cs     (of-fn f)]
                      (if (< (count cs) nfacts)
                        cs
                        (into [] (comp (mapcat #(reads/as-stored-with-functor (:index kb) %))
                                       (keep #(p/get-sentex (:records kb) %))
                                       (mapcat #(nat-read/fact-constants kb (:sentence %))))
                              preds))))
           all   (into (sorted-set-by #(compare (nm/name-key %1) (nm/name-key %2)))
                       (concat ks (mapcat of-fn fns) (mapcat valued fact-fns)))]
       (binding [wiring/*defer-settle?* true]
         (into [] (mapcat #(sync-value! kb % deferred)) all))))))

(defn- sync-queued-values!
  "Place what the constants queued on `:respell` for their correspondence derivations owe
  (`sync-values!`) and add the handles it made to `queued`, a running chain's queue, so a
  firing's mint takes its projection inside the run that minted it.  Inside
  `*rollback-scope*` it drops nothing and adds each constant owing a drop to `deferred`,
  which the run queues back for its settle, since a rollback keeps no record below the
  write's mark.  One scan of the queue while nothing is queued."
  [kb queued deferred]
  (let [q      (reasoning/respell kb)
        value? #(and (vector? %) (contains? #{:valued :valued-fn :valued-facts} (first %)))]
    (when (some value? @q)
      (let [[old _] (swap-vals! q #(into (empty %) (remove value?) %))
            taken   (filter value? old)
            by      (fn [t] (into [] (comp (filter #(= t (first %))) (map second)) taken))]
        (vswap! queued into (sync-values! kb (by :valued) (by :valued-fn) (by :valued-facts)
                                          (when *rollback-scope* deferred)))))))

(defn reconcile-formula-positions!
  "Bring the stored rules whose hold a `formula` position of one of `preds` decides
  (`nat/formula-position-rules`) to the spelling and the hold the declarations believed
  now read (`reconcile-reified-row!` with `redecide?`), and return the handles that are
  new content, for the agenda, or nil when no such rule is stored (docs/nat.md, The
  corresponding predicate).  Linear in the rules on `preds`."
  [kb preds]
  (when-let [rules (seq (nat/formula-position-rules kb preds))]
    (let [moved (volatile! [])
          memo  (volatile! {})
          new   (binding [wiring/*defer-settle?* true]
                  (into [] (mapcat #(reconcile-reified-row! kb memo moved nil identity (:id %) true))
                        rules))]
      (collect-respelled-orphans! kb @moved)
      new)))

(defn reconcile-stranded!
  "Re-spell the stored uses departed `natFormula` maps left naming their object constants
  (`nat/stranded-uses`), `maps` holding the departed `[k E]` pairs.  Each use is planned
  from its sentence with every constant expanded and each departed `k` written `E`
  (`nat/written-as`), so the write path's walk spells it again.  Returns the handles that
  are new content, or nil when no map left a use behind (docs/nat.md, A reifiable mark
  moving)."
  [kb maps]
  (let [maps     (nm/sort-by-content-key identity maps)
        departed (update-vals (group-by first maps) #(nat/authoritative-expression (map second %)))
        groups   (second
                  (reduce (fn [[seen acc] [k E]]
                            (let [us (into [] (remove #(contains? seen (:id %))) (nat/stranded-uses kb k E))]
                              [(into seen (map :id) us) (cond-> acc (seq us) (conj [E us]))]))
                          [#{} []]
                          maps))]
    (when (seq groups)
      (let [moved (volatile! [])
            memo  (volatile! {})
            pre   #(nat/written-as kb % departed)
            new   (binding [wiring/*defer-settle?* true]
                    (into []
                          (mapcat
                           (fn [[E us]]
                             (let [witness (mark-witness kb (first E))]
                               (into []
                                     (mapcat #(reconcile-reified-row! kb memo moved witness pre %))
                                     (map :id (nm/sort-by-content-key #(vector (sx/sentence-of %) (:context %)) us))))))
                          groups))]
        (collect-respelled-orphans! kb @moved)
        new))))

(defn- fire-rule
  "Apply a newly added rule over existing facts, at the rule's own strength.  `admit` is
  the arrival filter on the facts the join yields (`rule-arrival-admit`), nil for the
  full join a re-join runs.  `delta` is `planned-join`'s."
  ([kb rule-handle max-depth truncated] (fire-rule kb rule-handle max-depth truncated nil))
  ([kb rule-handle max-depth truncated admit] (fire-rule kb rule-handle max-depth truncated admit nil))
  ([kb rule-handle max-depth truncated admit delta]
   (let [{:keys [antecedents consequent] :as rule} (rule-fields kb rule-handle)]
     (reduce (fn [nh state]
               (into nh (:new (derive-conclusion kb rule state max-depth truncated))))
             []
             (planned-join kb (vec antecedents) {} (nm/functor consequent)
                           [{:bindings {} :handles [] :matched []}] admit *stop* delta)))))

(defn- fire-rule-bound
  "Re-join the rule at `rule-handle` once per binding map of `b0s`, each join starting
  from it, with no arrival filter."
  [kb rule-handle b0s max-depth truncated]
  (let [{:keys [antecedents consequent] :as rule} (rule-fields kb rule-handle)]
    (into []
          (comp (mapcat (fn [b0]
                          (planned-join kb (vec antecedents) b0 (nm/functor consequent)
                                        [{:bindings b0 :handles [] :matched []}] nil *stop*)))
                (mapcat #(:new (derive-conclusion kb rule % max-depth truncated))))
          b0s)))

(def ^:dynamic *moved-types*
  "`{rule-handle types}` while a settle re-joins the rules a separation or `nonempty` move
  queued (`special/recheck-on-separation`, `special/recheck-nonempty-readers`), else nil.
  A rule handle named here that reaches the agenda is joined over `types`
  (`fire-rule-over-types`) instead of over its extent, and a lazy-forward rule's readers
  are (`rejoin-lazy-readers-over-types`)."
  nil)

(defn- fire-rule-over-types
  "Re-join the rule at `rule-handle` over the types `moved` whose separations or
  nonemptiness moved: once per end, each variable end of a `disjoint` antecedent and the
  argument of a `nonempty` one, and per type of `moved`, in content order, with that end
  bound to the type.  A pair neither of whose types moved reads the separation it read
  when the rule was last joined, and a type not moved the answer, so the firings over them
  stand.  A ground end among `moved` re-joins the rule in full."
  [kb rule-handle moved max-depth truncated]
  (let [ends (into [] (comp (mapcat (fn [a]
                                      (cond (separation-literal? a) (rest a)
                                            (and (seq? a) (= 2 (count a)) (= 'nonempty (first a)))
                                            [(second a)])))
                            (distinct))
                   (:antecedents (rule-fields kb rule-handle)))]
    (if (some #(and (not (sx/variable? %)) (contains? moved %)) ends)
      (fire-rule kb rule-handle max-depth truncated)
      (fire-rule-bound kb rule-handle
                       (for [v ends :when (sx/variable? v), t (sort nm/compare-form moved)]
                         {v t})
                       max-depth truncated))))

(defn- delta-fire-rule
  "Re-join one rule over `calc`'s delta `moved`: `fire-rule` once per distinct antecedent
  `calc` answers, that one narrowed by `*qualitative-delta*`.  The plain `fire-rule` when
  the rule has no such antecedent or every context's delta is `:all`."
  [kb calc rule-handle rsx moved max-depth truncated]
  (let [qs (distinct (filter #(= (:name calc) (:name (qualitative-antecedent kb %)))
                             (:antecedent rsx)))]
    (if (or (empty? qs) (every? #(= :all %) (vals moved)))
      (fire-rule kb rule-handle max-depth truncated)
      (reduce (fn [nh q]
                (binding [*qualitative-delta* {:literal q :moved moved}]
                  (into nh (fire-rule kb rule-handle max-depth truncated))))
              []
              qs))))

(defn- rejoin-qualitative
  "Re-join the believed forward rules `rules` mentioning `calc` over its delta at each
  reader context, then record each context's baseline (`qcn-kb/note-joined`).  The
  baseline is the one read before the join, recorded whatever fired: a conclusion the
  join places is a datum that takes its own delta against it."
  [kb calc rules max-depth truncated]
  (let [deltas (into {} (map (fn [c] [c (qkb/join-delta kb calc c)]))
                     (calculus-contexts kb calc))
        moved  (update-vals deltas :moved)
        fired  (reduce (fn [nh rh]
                         (let [rsx (p/get-sentex (:records kb) rh)]
                           ;; forward-capable and believed, as `fire-rules-for` refuses on
                           ;; the record: the antecedent index posts on storage, and firing
                           ;; a rule labelled OUT still lands its reports and skolem records
                           (if (and rsx (rules/forward-sentex? rsx) (res/rule-believed? kb rh))
                             (into nh (delta-fire-rule kb calc rh rsx moved max-depth truncated))
                             nh)))
                       []
                       rules)]
    (doseq [[c d] deltas] (qkb/note-joined kb calc c (:baseline d)))
    fired))

(defn- permuting-rejoin-rules
  "The forward rules to re-join because `fact` is a permuting mark (`(symmetric P)`,
  `(commutative P)`, `(commutativeInArgs P …)`, `(commutativeInArgAndRest P n)`;
  `inherit/permuting-marks`).  Keys on `genls(P)`, and on the rules the term index keys by
  `P`, which hold every rule applying `P` below an antecedent literal (`res/nested-probes`).
  A symbol compare for every other datum.  See docs/inference.md, \"Full re-joins on an
  arriving datum\"."
  [kb fact]
  (when (and (sequential? fact) (next fact) (inherit/permuting-mark? (nm/functor fact)))
    (let [p   (first (nm/args fact))
          idx (:index kb)]
      (when (and (symbol? p) (not (sx/variable? p)))
        (not-empty
         (into (into #{} (mapcat #(reads/as-stored-rules-by-antecedent-global idx %))
                     (tax/genls-global (reasoning/taxonomy kb) p))
               (when (pos? (reads/stored-rule-count-global idx))
                 (filter #(:antecedent (p/get-sentex (:records kb) %))
                         (reads/as-stored-with-term idx p)))))))))

(defn- transitive-rejoin-rules
  "The forward rules to re-join because the arriving datum moved a transitive walk: the
  `(transitive P)` declaration, or an edge of a declared one (a fact on that predicate, a
  sub-predicate, or an `inverse` partner).  Keys on `P` itself, since the antecedent's own
  functor must be the declared one (`transitive-antecedent?`).  `bfn` is the functor of the
  sentence's underlying body.  Over-approximating on purpose.  See docs/inference.md, \"Full
  re-joins on an arriving datum\"."
  [kb fact bfn]
  (let [tx       (reasoning/taxonomy kb)
        walked?  #(and (symbol? %) (not (sx/variable? %))
                       (not (contains? provers/transitive-predicates %)))
        declared (when (and (sequential? fact) (= 2 (count fact))
                            (= 'transitive (nm/functor fact)))
                   (filter walked? (take 1 (nm/args fact))))
        ts       (filter walked? (tax/props tx :transitive))
        edges    (when (seq ts)
                   (let [ups (tax/genls-global tx bfn)]
                     (or (seq (filter ups ts))
                         (seq (filter #(contains? (tax/inverses-under tx %) bfn) ts)))))]
    (when-let [hit (seq (distinct (concat declared edges)))]
      (not-empty
       (into #{} (mapcat #(reads/as-stored-rules-by-antecedent-global (:index kb) %)) hit)))))

(defn- reflexive-rejoin-rules
  "The forward rules to re-join because the arriving datum is a `(reflexive P)` declaration
  on a calculus predicate, which gives the diagonal of `P`'s network a support
  (`qcn-kb/solve-with-support`): the rules with an antecedent on `P`, stated in every
  context, since placement decides where a firing lands."
  [kb fact]
  (when (and (sequential? fact) (= 2 (count fact)) (= 'reflexive (nm/functor fact)))
    (let [p (second fact)]
      (when (and (symbol? p) (qkb/calculus-for kb p))
        (not-empty (into #{} (reads/as-stored-rules-by-antecedent-global (:index kb) p)))))))

(defn- closure-rejoin-rules
  "The forward rules to re-join because the arriving datum is a `genl` or `genlCx` edge:
  the rules carrying an antecedent on the same relation, which the join answers from the
  closure (`solve-closure`).  A cover re-joins the rules reading `genl`
  (`special/closure-edge-relation`).  Runs only when a stored antecedent key names the
  relation."
  [kb fact]
  (when-let [f (special/closure-edge-relation fact)]
    (when (reads/stored-rule-key? (:index kb) f)
      (not-empty (into #{} (reads/as-stored-rules-by-antecedent-global (:index kb) f))))))

(defn- separation-denial-rejoins
  "The bound re-joins an arriving membership `fact`, `(S x)`, owes the rules with a
  negated antecedent `(not (T v))` on a type `T` a declaration separates from `S`
  (`tax/pair-separated?`, unscoped and with no exception read), as `{rule-handle #{b0}}`:
  `b0` binds `v` to `x`, or is `{}` for a ground `v` equal to `x`.  The rule index files
  the antecedent under `[:not T]`, which `(S x)` does not trigger.  Reads the rules stated
  in every context, since placement decides where a firing lands.  Nil for any other datum."
  [kb fact]
  (when (and (seq? fact) (= 2 (count fact)))
    (let [[s x] fact
          tx    (reasoning/taxonomy kb)]
      (when (and (symbol? s) (not= sx/not-functor s) (not (sx/variable? s))
                 (tax/separable? tx s))
        (let [idx (:index kb)
              ks  (filterv #(tax/pair-separated? tx s (second %)) (rules/stored-negated-keys idx))]
          (not-empty
           (reduce (fn [m [rh b0]] (update m rh (fnil conj #{}) b0))
                   {}
                   (for [k  ks
                         rh (reads/as-stored-rules-by-antecedent-global idx k)
                         a  (:antecedent (p/get-sentex (:records kb) rh))
                         :when (and (= k (rules/antecedent-key a)) (= 2 (count (second a))))
                         :let [v (second (second a))]
                         :when (or (sx/variable? v) (= v x))]
                     [rh (if (sx/variable? v) {v x} {})]))))))))

(defn- rejoin-in-full
  "Re-join in full every forward rule the arriving datum moved a preserved predicate for,
  newly declared symmetric, fed a `SupportingProver` a source it reads, gave a new hop to a
  transitive predicate's walk, or gave a new edge to the closure a closure antecedent reads.
  In full and not at a trigger position, since the arriving sentence need not unify with the
  antecedent it enabled.  Each arm is bounded by the rules with an antecedent on the predicate
  involved.  `delta` is `planned-join`'s, nil for the full join.  See docs/inference.md, \"Full
  re-joins on an arriving datum\"."
  ([kb rules max-depth truncated] (rejoin-in-full kb rules max-depth truncated nil))
  ([kb rules max-depth truncated delta]
   (reduce (fn [nh rh]
             (let [rsx (p/get-sentex (:records kb) rh)]
               ;; forward-capable and believed, as in `rejoin-qualitative`: the index posts on storage, so an un-believed rule reaches here
               (if (and rsx (rules/forward-sentex? rsx) (res/rule-believed? kb rh))
                 (into nh (fire-rule kb rh max-depth truncated nil delta))
                 nh)))
           []
           rules)))

(defn- owe-computed-rejoins
  "Owe each rule of `rules` the re-join a datum `datum` puts it in front of, on a source
  predicate (`special/computed-reading-rules`) or read by a lazy-forward rule's conclusion
  (`lazy-readers`).  Inside a `with-deferred-settle` batch the owed set goes to
  `*batch-rejoins*` and nothing is joined until the batch settles.  Inside a run
  (`*computed-rejoins*`) a rule not already owed one gets a marker queued behind the datum,
  and the datum joins the rule's owed set; `filterable?` false
  (`provers/support-delta-source?`) makes that set `:all`.  Outside both, the rules are
  re-joined in full at once.  Returns the handles that placed."
  [kb rules datum filterable? max-depth truncated]
  (if-let [^java.util.Map owed (when wiring/*defer-settle?* *batch-rejoins*)]
    (do (doseq [rh rules] (owe-batch-rejoin owed rh (when filterable? [datum])))
        [])
    (if-let [{:keys [^java.util.Map owed queue]} *computed-rejoins*]
      (do (doseq [rh rules]
            (let [cur (.get owed rh)]
              (when (nil? cur) (vswap! queue conj [::owed-rejoin rh]))
              (.put owed rh (if (and filterable? (not= :all cur)) (conj (or cur #{}) datum) :all))))
          [])
      (rejoin-in-full kb rules max-depth truncated))))

(defn- owed-rejoin?
  "Is the agenda entry `d` a re-join marker `owe-computed-rejoins` queued, not a handle?"
  [d]
  (vector? d))

(defn- run-owed-rejoin
  "Run the re-join the marker `[::owed-rejoin rh]` stands for: the rule joined in full,
  keeping past its computed antecedents only the rows that rest on a datum that owed it
  (`planned-join`'s `delta`), or every row when one could not be filtered.  The marker
  stands behind every datum that owed it, so each of their facts is stored when the join
  reads.  A row whose computed answer rests on no datum of the set was answered before
  the earliest of them, and the join that datum's predecessor owed placed it."
  [kb [_ rh] max-depth truncated]
  (let [delta (.remove ^java.util.Map (:owed *computed-rejoins*) rh)]
    (rejoin-in-full kb [rh] max-depth truncated (when (set? delta) delta))))

(defn- stale-closure-rejoins
  "The rules of `rules` that this run has not re-joined in full at the current
  `special/taxonomy-generations` value, recording each forward, believed one at that value
  in `*closure-rejoins*`.  Outside a run, `rules` unchanged."
  [kb rules]
  (if-let [^java.util.HashMap seen (when rules *closure-rejoins*)]
    (let [gens (special/taxonomy-generations kb)]
      (not-empty
       (into #{}
             (filter (fn [rh]
                       (when (not= gens (.get seen rh))
                         (let [rsx (p/get-sentex (:records kb) rh)]
                           (when (and rsx (rules/forward-sentex? rsx) (res/rule-believed? kb rh))
                             (.put seen rh gens)))
                         true)))
             rules)))
    rules))

(defn- fire-rules-for
  "Fire every forward rule a newly asserted fact can trigger, strict and defeasible alike.
  Candidate rules are keyed by the fact's predicate and its supertypes, and each fires at its
  own strength (`provers/firing-strength`).  A default conclusion is placed unconditionally
  and defeat is decided by `settle`, so firing order affects cost and never what is derived.
  The depth guard applies equally and reaches the run's `:truncated?` flag."
  [kb datum max-depth truncated]
  (let [fact     (:sentence (p/get-sentex (:records kb) datum))
        ffn      (nm/functor fact)
        ;; read once per datum, not per candidate position: what makes the mirror true is
        ;; the fact's own `symmetric` declaration, and every position asks the same fact
        mirror   (symmetric-mirror kb fact)
        ;; and, at any arity, the components the fact's own predicate licences — read
        ;; once per datum for the same reason the mirror is
        comps    (commuting-components-of kb fact)
        ;; a positive fact's predicate and its supertypes; a negative fact's `[:not q]` keys for
        ;; the specs `q` of its body's predicate, each the closure intersected with the rule-key
        ;; set, read from the smaller side (`rules/trigger-keys`)
        preds    (rules/trigger-keys (reasoning/taxonomy kb) fact (:index kb))
        rhs      (into #{} (mapcat #(reads/as-stored-rules-by-antecedent-global (:index kb) %)) preds)
        ;; a fact moving a calculus's network re-joins every rule on a predicate that calculus
        ;; answers (`rejoin-qualitative`; docs/qcn.md, "Forward chaining too")
        bfn      (if (= sx/not-functor ffn) (nm/functor (kb/body-under-not fact)) ffn)
        qrules   (when-let [cs (qkb/calculi-triggered-by
                                kb (if (and (= 'genl ffn) (= 3 (count fact))) (nth fact 2) bfn))]
                   (mapv (fn [c]
                           [c (into #{} (mapcat #(reads/as-stored-rules-by-antecedent-global (:index kb) %))
                                    (:predicates c))])
                         cs))
        qrhs     (when qrules (not-empty (into #{} (mapcat second) qrules)))
        ;; a sentence can move what a preserved predicate licenses without being on that predicate;
        ;; `inherit/rejoin-rules` reads the declarations to say which rules, and answers nil off two
        ;; extent counts for a KB that declares none
        prhs     (inherit/rejoin-rules kb fact)
        ;; a permuting mark datum changes which tuples a P antecedent reaches (`permuting-rejoin-rules`); a symbol compare otherwise
        srhs     (permuting-rejoin-rules kb fact)
        ;; And once more for a prover rather than for the matcher: a datum on a predicate
        ;; a `SupportingProver` reads moves what a computed antecedent answers, and no
        ;; walk from `conversionFactor` reaches `quantityGreaterThan`.
        crhs     (special/computed-reading-rules
                  kb bfn (if (= sx/not-functor ffn) (kb/body-under-not fact) fact))
        ;; And once more for the walk rather than for the table: an arriving edge makes
        ;; pairs a `(transitive P)` antecedent reaches, which the trigger index does not
        ;; offer; a calculus predicate's `(reflexive P)` supports its diagonal.
        trhs     (not-empty (into #{} cat [(transitive-rejoin-rules kb fact bfn)
                                           (reflexive-rejoin-rules kb fact)]))
        ;; ...and for a cached closure: an arriving `genl` / `genlCx` edge adds pairs a
        ;; closure antecedent reaches through the edges already stored
        grhs     (stale-closure-rejoins kb (closure-rejoin-rules kb fact))
        drhs     (when (jtms/in? (reasoning/tms kb) datum) (separation-denial-rejoins kb fact))
        ;; each candidate's record is read once per datum, by the lazy-forward check and the trigger
        rsx-of   (let [m (java.util.HashMap.)]
                   (fn [h] (or (.get m h)
                               (let [r (p/get-sentex (:records kb) h)] (.put m h r) r))))
        joined   (cond->> rhs
                   qrhs (remove qrhs)
                   prhs (remove prhs)
                   srhs (remove srhs)
                   crhs (remove crhs)
                   trhs (remove trhs)
                   grhs (remove grhs))
        lrhs     (lazy-readers kb joined rsx-of)
        lmoved   (lazy-readers kb (concat qrhs prhs srhs crhs trhs grhs (keys drhs)) rsx-of)
        trigger  (cond->> joined
                   lrhs   (remove lrhs)
                   lmoved (remove lmoved))
        ;; forward-capable *and believed*: the antecedent index posts on storage, so a
        ;; rule whose support has gone is still a candidate here and is refused on its
        ;; record rather than by the lookup (`res/rule-believed?`)
        forward? (fn [rh rsx] (and rsx (rules/forward-sentex? rsx)
                                   (res/rule-believed? kb rh)))
        ;; A rule that reached the agenda after the datum enumerates the datum's firings from
        ;; its own full join (`rule-arrival-admit`), so the datum leaves them to it: only where
        ;; that join is sure to find the datum (believed, and no mark of its own rearranges its
        ;; match, `read-marks`).
        later-rule? (when-let [^java.util.Map arrivals *agenda-arrivals*]
                      (when-let [at (.get arrivals datum)]
                        (when (and (nil? mirror) (empty? comps)
                                   (jtms/in? (reasoning/tms kb) datum))
                          (let [at (long at)]
                            (fn [rh] (let [a (.get arrivals rh)]
                                       (and (some? a) (> (long a) at))))))))]
    (into
     (reduce
      (fn [nh rh]
        (let [rsx (rsx-of rh)]
          (if (or (not (forward? rh rsx)) (and later-rule? (later-rule? rh)))
            nh
            ;; The trigger match runs over the record's own antecedents, and the rule-fields map is
            ;; built only once a position unifies, since for a broad type most candidates unify at
            ;; none: a per-firing cost, not a per-candidate one.
            (let [antecedents (:antecedent rsx)
                  cpred       (nm/functor (:consequent rsx))
                  rule        (delay (rule-fields-of kb rh rsx))]
              (reduce (fn [nh2 i]
                        (reduce
                         (fn [nh3 b0]
                           ;; a trigger binding that fixes the conclusion to the datum itself makes only firings
                           ;; `derive-conclusion` places nothing for (`restates-an-antecedent?`); skip the join
                           (if (and (= cpred ffn)
                                    (= fact (res/substitute (:consequent rsx) b0))
                                    (not (deferred-antecedent? kb (nth antecedents i))))
                             nh3
                             (reduce (fn [nh4 state]
                                       (into nh4 (:new (derive-conclusion kb @rule state max-depth truncated))))
                                     nh3
                                     (complete-antecedents
                                      kb antecedents i datum b0
                                      ;; only the fact's own marks and its compounds' rearrange it
                                      (if (or mirror comps
                                              (next (res/nested-probes kb (nth antecedents i)))
                                              (seq (res/mention-probes kb (nth antecedents i))))
                                        (read-marks kb (nth antecedents i) b0 datum nil)
                                        [[]])
                                      cpred))))
                         nh2
                         (trigger-bindings kb (nth antecedents i) fact mirror comps)))
                      nh
                      (range (count antecedents)))))))
      []
      trigger)
     (concat
      (when qrhs
        (into [] (mapcat (fn [[c rs]]
                           (when (seq rs) (rejoin-qualitative kb c rs max-depth truncated))))
              qrules))
      (when (seq prhs) (rejoin-in-full kb prhs max-depth truncated))
      (when (seq srhs) (rejoin-in-full kb srhs max-depth truncated))
      (when (seq crhs)
        (owe-computed-rejoins kb crhs datum (and (not= sx/not-functor ffn)
                                                 (provers/support-delta-source? kb bfn fact))
                              max-depth truncated))
      (when (seq trhs) (rejoin-in-full kb trhs max-depth truncated))
      (when (seq grhs) (rejoin-in-full kb grhs max-depth truncated))
      (when drhs
        (into [] (mapcat (fn [[rh b0s]]
                           (when (and (forward? rh (rsx-of rh))
                                      (not (and later-rule? (later-rule? rh))))
                             (fire-rule-bound kb rh b0s max-depth truncated))))
              drhs))
      (when lrhs
        (owe-computed-rejoins kb lrhs datum (and (not= sx/not-functor ffn)
                                                 (not (contains? tax/edge-installing-functors bfn)))
                              max-depth truncated))
      (when lmoved (owe-computed-rejoins kb lmoved datum false max-depth truncated))))))

(defn- lazy-type-ends
  "The terms the antecedent `ante` of a reader puts at the `nonempty` arguments of the
  lazy-forward rule `lsx` once `lsx`'s consequent is unified with it; nil when `lsx` reads
  no `nonempty` or a separation, when a variable argument is no argument of the
  consequent, or when `ante` is not on the consequent's functor at its length."
  [lsx ante]
  (let [c    (:consequent lsx)
        args (keep #(when (and (seq? %) (= 2 (count %)) (= 'nonempty (first %))) (second %))
                   (:antecedent lsx))
        at   (into {} (map-indexed (fn [i t] [t i])) (rest c))]
    (when (and (seq args) (not-any? separation-literal? (:antecedent lsx))
               (sequential? ante) (= (first c) (first ante)) (= (count c) (count ante))
               (every? #(or (not (sx/variable? %)) (contains? at %)) args))
      (mapv #(if (sx/variable? %) (nth ante (inc (long (at %)))) %) args))))

(defn- rejoin-lazy-readers-over-types
  "Re-join the readers `rs` (`lazy-readers`) of the lazy-forward rule `lsx` over the types
  `moved` whose nonemptiness moved.  A believed forward reader proving `lsx`'s literal
  directly is joined once per variable it puts at a `nonempty` argument of `lsx`
  (`lazy-type-ends`) and per type of `moved`, in content order, as `fire-rule-over-types`
  joins a rule's own `nonempty` argument; a ground end among `moved` joins it in full.  Any
  other reader owes the re-join in full (`owe-computed-rejoins`)."
  [kb lsx rs moved max-depth truncated]
  (let [f     (nm/functor (:consequent lsx))
        plans (for [rh (sort rs)
                    :let [rsx (p/get-sentex (:records kb) rh)
                          as  (when (and rsx (rules/forward-sentex? rsx))
                                (filter #(and (sequential? %) (= f (first %))) (:antecedent rsx)))
                          es  (map #(lazy-type-ends lsx %) as)]]
                [rh (when (and (seq as) (every? some? es)) (vec (distinct (apply concat es))))])
        full  (into [] (keep (fn [[rh ends]] (when (nil? ends) rh))) plans)
        types (sort nm/compare-form moved)]
    (into (if (seq full) (owe-computed-rejoins kb full (:id lsx) false max-depth truncated) [])
          (mapcat (fn [[rh ends]]
                    (when (and ends (res/rule-believed? kb rh))
                      (if (some #(and (not (sx/variable? %)) (contains? moved %)) ends)
                        (fire-rule kb rh max-depth truncated)
                        (fire-rule-bound kb rh (for [v ends :when (sx/variable? v), t types] {v t})
                                         max-depth truncated)))))
          plans)))

(defn- process-datum
  "In a global chain, a rule datum fires if it is forward-capable — defeasible or
  not (a backward/inert rule never forward-chains).  A fact fires the rules keyed
  by it.  A re-join marker runs the re-join it stands for (`run-owed-rejoin`).  Binds
  `*qcn-contexts*` and holds the resident values fixed (`observe/with-held-values`) for
  the datum (docs/qcn.md, \"One thing the clock cannot supply\")."
  [kb datum max-depth truncated]
  (observe/with-held-values
    (binding [*qcn-contexts* (atom {})]
      (let [sx (when-not (owed-rejoin? datum) (p/get-sentex (:records kb) datum))]
        (cond
          (owed-rejoin? datum) (run-owed-rejoin kb datum max-depth truncated)
          (rules/rule? sx)
          ;; direction and defeasibility are read off the record; a defeasible rule fires at
          ;; :default.  Belief is asked here as in `fire-rules-for`, since a derived rule can arrive
          ;; already defeated.
          (cond
            (and (rules/forward-sentex? sx) (res/rule-believed? kb datum))
            (if-let [moved (get *moved-types* datum)]
              (fire-rule-over-types kb datum moved max-depth truncated)
              (fire-rule kb datum max-depth truncated (rule-arrival-admit datum)))
            (rules/lazy-sentex? sx)
            (do (some-> *lazy-rules* (vreset! nil))
                (if-let [rs (lazy-readers kb [datum] #(if (= datum %) sx (p/get-sentex (:records kb) %)))]
                  (if-let [moved (get *moved-types* datum)]
                    (rejoin-lazy-readers-over-types kb sx rs moved max-depth truncated)
                    (owe-computed-rejoins kb rs datum false max-depth truncated))
                  []))
            :else [])
          ;; a superseded fact is the one unbelieved datum that does not fire; its
          ;; restatement fires instead (docs/equality.md, "What a merge does")
          (jtms/superseded? (reasoning/tms kb) datum) []
          :else (fire-rules-for kb datum max-depth truncated))))))

(defn chain
  "Semi-naive fixpoint forward chaining seeded with `seed`, strict and defeasible rules on
  one agenda.  A chain bound `opts` does not name is the one `call-with-stop` holds in force
  (`*bounds*`), else `default-chain-opts`'.  `opts` may carry `:on-progress`, called about
  four times a second (`:progress-every-ms`) with `{:derived n :pending n}`; it may throw, which
  aborts the run (how a loader cancels one) and leaves the prefix derived, not a corrupt KB.  A bound in force (`*stop*`) or
  `:max-derivations` ends the run: inside `*rollback-scope*` with `:interrupted`, outside it or
  under `*keep-on-stop*` without a throw, returning `:truncated?` with `:bound` naming
  `:max-derivations`, `:max-ms` or `:stop?`.  Progress reports at the agenda loop and at each
  firing (`*tick*`); one unproductive join reports nothing until it ends, bounded by the
  extent it scans."
  [kb seed opts]
  ;; The generative join is `settle-phases`' `:chaining` centre — a bulk load fires it per
  ;; assert, a `recover` not at all.  Wraps `chain` alone: `chain-all` and the settle
  ;; re-chain both route through here, and the span nests cleanly when they do.
  (phases/with-phase :chaining
    (let [{:keys [max-depth max-term-depth max-derivations on-progress progress-every-ms]}
          (merge default-chain-opts *bounds* opts)
          term-bound (when max-term-depth
                       {:max max-term-depth :cut (volatile! 0)})
          interval  (* (long (or progress-every-ms default-progress-ms)) 1000000)
          truncated (atom false)
          ;; the run's own counters, off the loop vars so a report from inside a datum sees
          ;; the same numbers the loop does.  Chaining is single-threaded (the one-writer
          ;; contract), so a volatile is the whole of the synchronization needed.
          placed    (volatile! 0)
          pending   (volatile! (count seed))
          reported  (volatile! (System/nanoTime))
          report!   (fn [] (vreset! reported (System/nanoTime))
                      (on-progress {:derived @placed :pending @pending}))
          due?      (fn [] (>= (- (System/nanoTime) @reported) interval))
          ;; the agenda's own order (`*agenda-arrivals*`); a fresh map per run, since a nested run
          ;; (an `:on-progress` callback may start one) has its own agenda
          arrivals  (when *suppress-duplicate-firings* (java.util.HashMap.))
          arrived   (volatile! 0)
          arrive!   (fn [hs]
                      (when arrivals
                        (doseq [h hs] (.put ^java.util.Map arrivals h (vswap! arrived inc)))))
          ;; the seeds the datum's writes queued (`*run-queue*`) and the correspondence derivations
          ;; of the constants they queued, less any a refused write took back; they count against
          ;; `max-derivations`, since a chain of mints can place nothing new
          queued    (volatile! [])
          written   (volatile! 0)
          ;; the constants whose value derivations owe a drop the run left to its settle
          deferred  (volatile! #{})
          drain!    (fn []
                      (sync-queued-values! kb queued deferred)
                      (let [hs @queued]
                        (if (empty? hs)
                          hs
                          (let [live (filterv #(p/get-sentex (:records kb) %) hs)]
                            (vreset! queued [])
                            (vswap! written + (count live))
                            live))))
          ;; a run whose stop throws goes on at the cap and stops past it, so a run that
          ;; makes exactly `max-derivations` stores them; one that keeps what it placed
          ;; (outside a rollback scope, or under `*keep-on-stop*`) stops at the cap
          over      (if (and *rollback-scope* (not *keep-on-stop*)) 1 0)
          spent?    (fn [] (and max-derivations
                                (>= (+ (long @placed) (long @written))
                                    (+ (long max-derivations) over))))
          ;; the computed re-joins owed and not yet run, and the markers standing for
          ;; them, which join the agenda behind the datum that queued them
          rejoins   (let [^java.util.Map owed (or (::owed opts) {})]
                      {:owed (java.util.HashMap. owed) :queue (volatile! [])})
          owed!     (fn []
                      (let [ms @(:queue rejoins)]
                        (when (seq ms) (vreset! (:queue rejoins) []))
                        ms))]
      ;; the tick is bound whether or not anybody listens: it also counts what the run derived.
      ;; The handle cache is engaged for the same scope (a conclusion reached k ways would
      ;; otherwise be k trie walks); a removal inside a run forgets its entry
      ;; (`observe/forget-handle!`).  The justification dedup index rides the scope too, is
      ;; cleared by `jtms/retract!`, `jtms/sweep!` and `jtms/drop-justification!`, and is scoped to
      ;; this KB's TMS.  The arrival ledger is the agenda's own order: a datum gets its number as
      ;; it is enqueued.
      (observe/with-handle-cache
        (jtms/with-dedup-cache (reasoning/tms kb)
          (binding [*tick* (fn [n]
                             (vswap! placed + n)
                             (when (and on-progress (due?)) (report!)))
                    ;; the fourth thing on this scope: a per-functor verdict on whether the handle cache is
                    ;; authoritative (the store held nothing under the functor when the run began), so a novel
                    ;; conclusion of a chain-only predicate skips the trie walk (`kb/find-sentex-handle`).
                    ;; Fresh per run.  Armed only for a bulk frontier (`kb/chain-authority-min-frontier`);
                    ;; an incremental assert's one-fact seed concludes too little to repay the probe, so it stays
                    ;; nil and walks the trie.
                    kb/*chain-authoritative-functors* (when (>= (count seed)
                                                                kb/chain-authority-min-frontier)
                                                        (java.util.HashMap.))
                    ;; the KB's registered evaluatables, read once: the registry is fixed for a run, and the
                    ;; join reads this set per antecedent (`deferred-antecedent?`); a nested run rebinds it
                    *evaluatable-preds* (provers/evaluatable-preds kb)
                    ;; whether the KB declares any preservation (`*declarations-cell*`), a fresh cell per run
                    *declarations-cell* (volatile! nil)
                    *lazy-rules* (volatile! nil)
                    ;; One full closure re-join per rule per value of the taxonomy generations: a
                    ;; departing `genlCx` edge re-chains every `genl` fact above it, each the same rules.
                    *closure-rejoins* (java.util.HashMap.)
                    *agenda-arrivals* arrivals
                    *term-bound* term-bound
                    *run-queue* {:records (:records kb) :seeds queued}
                    *computed-rejoins* rejoins]
            (arrive! seed)
            (loop [agenda (into clojure.lang.PersistentQueue/EMPTY seed)]
              (if (or (empty? agenda) (spent?)
                      (and (seq agenda) (stopped? *stop*)))
                (do (when (seq @deferred)
                      (swap! (reasoning/respell kb) into (map #(vector :valued %)) @deferred))
                    (when (and *rollback-scope* (not *keep-on-stop*))
                      (cond (spent?)                       (interrupted! :max-derivations)
                            (some-> *stop* :hit deref)     (interrupted! (stop-bound *stop*))))
                    (vreset! pending (count agenda))
                    (when on-progress (report!))
                    ;; a check that found the bound reached was passed a datum, a firing
                    ;; or a row, and left it unmade
                    (let [hit   (some-> *stop* :hit deref)
                          bound (cond (spent?) :max-derivations
                                      hit      (stop-bound *stop*))]
                      (cond-> {:derived @placed :truncated? (boolean (or @truncated bound))}
                        (some-> term-bound :cut deref pos?) (assoc :term-cut @(:cut term-bound))
                        bound                               (assoc :bound bound))))
                (let [_       (heap-check!)
                      d       (peek agenda)
                      fired   (process-datum kb d max-depth truncated)
                      new-hs  (into (drain!) fired)
                      _       (arrive! new-hs)
                      agenda' (-> (pop agenda) (into new-hs) (into (owed!)))]
                  (vreset! pending (count agenda'))
                  (when (and on-progress (due?)) (report!))
                  (recur agenda'))))))))))

(defn rerecord-refusals!
  "Rebuild the refusal record by re-firing every believed forward rule that carries a
  re-checkable block condition (`reads/watched-rules`).  Returns the chain result, or nil for a
  KB where no rule carries one.  A closed-extent negative antecedent that does not hold
  re-records its refusal; an `exceptWhen` or `unknown` that holds records nothing (the firing
  is placed with its guard defeat).  `recover`'s half of the record: a refused firing left
  no justification, so the stored justifications cannot restore it and re-firing re-decides
  it.  Runs after the settle that establishes belief, since a refusal is a claim about it.  `!` because it discards the record it replaces.  Re-fires under
  the default bounds, so rebuilt entries record no derivation-depth bound; docs/exceptions.md
  states the one case this differs from the live session."
  [kb]
  (when-let [watched (seq (reads/watched-rules (:index kb)))]
    (reset! (reasoning/refused kb) {})
    (let [live (filterv (fn [rh]
                          (let [rsx (p/get-sentex (:records kb) rh)]
                            (and rsx (rules/rule? rsx) (rules/forward-sentex? rsx)
                                 (jtms/in? (reasoning/tms kb) rh))))
                        watched)]
      (when (seq live)
        (with-open [r (progress/start ::rerecord-refusals "recover: re-fire the rules that can refuse (derivations)" nil)]
          (chain kb live {:on-progress (progress/on-progress r)}))))))

(defn resync-arity-classes!
  "Sync the class memberships of every stored membership of a type below an exact-arity
  class (`sync-arity-classes!`), chain from the new ones, and answer whether one was
  placed.  `recover`'s half of the derivation: a store written with no belief holds no
  justification under `arity-class-informant`, and its closing settle replays only the
  stored ones."
  [kb]
  (arity/take-class-ends! kb)
  (let [tax  (reasoning/taxonomy kb)
        idx  (:index kb)
        recs (:records kb)
        ts   (into #{} (comp (mapcat #(tax/specs-global tax %)) (remove arity/exact-classes))
                   arity/exact-classes)
        ms   (with-open [r (progress/start ::arity-memberships "recover: read the arity memberships"
                                           nil)]
               (into [] (filter #(some? (arity/membership-of (p/get-sentex recs %))))
                     (progress/each r (mapcat #(reads/as-stored-with-functor idx %)
                                              (nm/sort-by-content-key nm/print-key compare ts)))))
        {:keys [new violations]} (if (seq ms)
                                   (with-open [_ (progress/start ::sync-arity-classes
                                                                 "recover: derive the arity class memberships"
                                                                 nil)]
                                     (sync-arity-classes! kb ms))
                                   {:new []})]
    (violations/report kb violations)
    (when (seq new)
      (with-open [r (progress/start ::resync-arity-classes "recover: chain from the arity class memberships (derivations)" nil)]
        (chain kb new {:on-progress (progress/on-progress r)})))
    (boolean (seq new))))

(defn- run-all
  "`chain-all`'s run: a new run in `chain-stats`, the result stashed there."
  [kb seed opts]
  (swap! (reasoning/chain-stats kb) update :runs inc)
  (let [started (System/nanoTime)
        result  (chain kb seed opts)]
    (swap! (reasoning/chain-stats kb) assoc :last result)
    ;; the counting is inside the payload, which Trove builds as a delay: a run that is
    ;; not being watched pays the `nanoTime` above and nothing else
    (trove/log! {:level :debug :id ::chain-run
                 :data (assoc result
                              :run  (:runs @(reasoning/chain-stats kb))
                              :seed (count seed)
                              :ms   (quot (- (System/nanoTime) started) 1000000))})
    (when (:truncated? result)
      (trove/log! {:level :warn :id ::chain-truncated
                   :msg "forward chaining was truncated (max-depth, max-derivations or the caller's bound) — conclusions are missing"
                   :data result}))
    (when (:term-cut result)
      (trove/log! {:level :info :id ::term-cut
                   :msg "firings that build terms nested past :max-term-depth were not placed"
                   :data result}))
    result))

(defn run-batch-rejoins
  "Run the re-joins `owed` (`*batch-rejoins*`' map) stands for in one chaining run, each
  as `run-owed-rejoin` runs a marker.  Nil when `owed` is nil or empty."
  [kb ^java.util.Map owed]
  (when (and owed (not (.isEmpty owed)))
    (let [m (java.util.HashMap. owed)]
      (.clear owed)
      (run-all kb (mapv #(vector ::owed-rejoin %) (sort (keys m))) {::owed m}))))

(defn chain-all
  "One fixpoint from `seed`, strict and defeasible rules on the same agenda
  (`fire-rules-for`).  Inside a run over the same store, `seed` is queued for that run
  (`*run-queue*`) and no run opens.  Opens a new run in `chain-stats` and stashes the result
  there, warning when the run was truncated.  Internal callers discard `:truncated?`, so the
  warning is how a depth-capped run's lost conclusions surface.  The ledger accumulates
  across runs.  At `:debug` every run logs what it did."
  [kb seed opts]
  (if-let [q (when (identical? (:records kb) (:records *run-queue*)) (:seeds *run-queue*))]
    (do (vswap! q into seed) {:derived 0 :truncated? false})
    (run-all kb seed opts)))

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :R11 :label "Chaining run memos" :kind :pass :keyed-by :value :reads [:index :records]
  :holds-content? false
  :retired-by {} :computed :pass :imaged? false :var #'*declarations-cell*
  :note "`*agenda-arrivals*`, `*declarations-cell*`, `*closure-rejoins*`, `*computed-rejoins*`, `*lazy-rules*`, `*evaluatable-preds*` for one run, `*batch-rejoins*` for one `with-deferred-settle` batch, `term-cut?`'s nesting memo for one firing and `*qcn-contexts*` for one datum"})
