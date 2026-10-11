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
  (:require [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.membership :as membership]
            [vaelii.impl.decide.negation :as negation]
            [vaelii.impl.decide.related :as related]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.except :as exc]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.plan :as plan]
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
  "max-depth bounds derivation depth to catch productive infinite recursion;
  max-derivations is a hard backstop on a single chain run."
  {:max-depth 64 :max-derivations 100000})

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

(def ^:dynamic *matcher*
  "How the forward join looks up the stored facts satisfying a **non-trigger**
  antecedent — `(fn [kb pattern context] -> seq of [handle bindings …])`, returning
  exactly what `res/match-pattern` does.

  The default is `res/match-pattern` (the count-aware trie), which is the reference
  path and leaves forward chaining unchanged.  `vaelii.impl.rete` binds this to a RAM
  alpha-memory matcher that answers the same set through an index on argument values,
  so a non-trigger antecedent with a leading variable — `(parentOf ?x Pi)` — is a
  hash lookup rather than a full functor scan.  The *set* it returns is identical
  (proven by the rete oracle), so every downstream behaviour is the reference's; only
  the candidate lookup changes.  This is the sole extension point the incremental matcher needs,
  because the trigger match (`match1`) is already selective and everything else —
  placement, exceptions, the definitional checks, justification dedup — is reused
  verbatim.  See docs/inference.md, \"Incremental rule matching\".

  With the reference bound, a substituted antecedent that has a bound indexable
  argument **and a functor with sub-predicates** is read through
  `res/matches-hierarchical` instead (`join-matches`) — the same set by an argument
  lead rather than a trie walk per sub-predicate.  Binding this var to anything else
  switches that off, so the extension point's caller sees every non-trigger antecedent."
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
  "A mutable `{handle -> arrival}` map — the position at which each datum joined this
  run's agenda — or nil, and then nothing is suppressed.

  **This decides work, not belief.**  A rule `a(x,y) <- b1(x,z), b2(z,y)` is triggered
  by its `b1` datum at position 0 and by its `b2` datum at position 1, and both
  enumerate the same pair: the second runs the whole join, rebuilds the same
  conclusion, resolves the same placement contexts, and is thrown away by
  `jtms/has-justification?`.  Ordering the agenda's datums lets one of the two skip the
  work — the firing that survives is *identical* whichever side makes it (same
  bindings, same antecedent set, same justification), so the derived set and its
  supports are unchanged by construction.  The **rule** is a participant as well: a
  seeded run puts the rule's own datum on the agenda beside its facts, and its full join
  would enumerate every firing again, so its arrival is compared too
  (`rule-arrival-admit`, and the skip in `fire-rules-for`).  Nothing here is read when
  belief is computed, and no tie-break anywhere keys on it: the engine's rule that belief never
  tie-breaks on a handle is untouched, because this is not consulted about belief.

  **Arrival order, not handle order**, and the difference is the whole correctness
  argument.  For a datum the run itself derives the two agree — handles are allocated
  in creation order and a new conclusion is enqueued as it is placed — but a datum put
  **back** on the agenda has an old handle and a fresh arrival: a fact revived from OUT,
  a fact newly matchable under a derived `genl` edge (`special/subsumption-seeds`), a
  seed list in whatever order `jtms/in-datums` produced.  Keyed on arrival, such a
  datum sorts *after* the partner that was already processed, so it is the one that
  enumerates the pair, and the pair is enumerated.  Keyed on the handle it would sort
  before it and the pair would be lost.

  A handle the run never enqueued has **no** arrival and is never suppressed against:
  nothing else will enumerate its combinations, so they are all made here.  That covers
  a sentex some other write placed while the run was going — a migrated twin the caller
  has not seeded yet — and every join run outside a chaining run at all.  A
  **disbelieved** trigger declines the filter outright, for the reason `arrival-admit`
  states.

  Bound by `chain` for the length of a run, like the handle cache and the dedup index,
  and it is the agenda that bounds its size.  A `java.util.HashMap` rather than an atom
  because the engine is single-writer and this is read once per candidate the join
  yields."
  nil)

;; ---- exceptWhen: evaluating the exception -------------------------------
;; The exception is **any closed level-6 query** once the rule's bindings are
;; substituted in.  Level 6 (`:solved`) is the full prover stack *minus* rule
;; backchaining, so an exception reaches through genl specificity, the genlCx
;; visibility closure, the transitive / symmetric / inverse metadata, disjointness and
;; the evaluables — but never invokes an unbounded proof search from inside the
;; relabel loop.  See docs/exceptions.md, "The exception is a query, not a literal".

(defn exception-holds?
  "Does `except` — a rule's exception, a vector of literals — hold under `bindings`,
  evaluated in `pctx`, the context the conclusion would be placed in?

  Three properties make this cheap, and each is required:

  * **Closed.**  Every exception variable is bound by an antecedent (enforced in the
    `sentex` constructor), so substitution leaves a *ground* question.  The conjuncts
    therefore share nothing and need no join — each is an independent existence check,
    and **all** must hold.
  * **One answer suffices.**  The levels stack is lazy throughout, so `first` stops
    the query at its first result rather than enumerating an extent.
  * **An unanswerable exception does not hold**, and the rule fires.  That is the
    open-world reading, and it matches `arg`, where an argument whose type is
    unknown cannot violate a constraint: blocking on \"cannot tell\" would let a
    missing fact silently suppress knowledge.

  An empty / absent exception never holds, so an ordinary rule takes no cost here.

  Defined in `vaelii.impl.provers` because the backward chainers need exactly the same
  judgement; `pctx` here is the conclusion's placement context, where backward passes
  the query's."
  [kb except bindings pctx]
  (provers/exception-holds? kb except bindings pctx))

;; ---- negation-as-failure antecedents ------------------------------------
;; An `(unknown S)` antecedent is `exceptWhen` inlined per-literal: the rule does not
;; conclude for a binding under which `S` is derivable.  It shares the exception's
;; evaluator — a closed level-6 existence check — and its whole block / sweep / revive
;; machinery, differing only in polarity and combination: each `unknown` is an
;; *independent* block condition (block if **any** inner holds), where an exception's
;; conjuncts are one condition (block if **all** hold).  Nothing is stored; the inner
;; query is re-evaluated on the same triggers.  See docs/naf.md.

(defn- unknown-inner-holds?
  "Does the query inside an `(unknown …)` antecedent hold under `bindings`, evaluated
  in `pctx`?  Run exactly like an exception — `provers/exception-holds?` over the
  query's conjuncts — so `unknown` and `exceptWhen` share one level-6 evaluator and
  cannot drift; a nested `thereExists` is dispatched to its prover from there.  When it
  holds, `S` is derivable, so `(unknown S)` is false and the firing is blocked.

  A conjunctive query is the same block-if-**all**-hold the exception's conjuncts are,
  and it is **joined** (`provers/conjunction-solutions`): a ground conjunction's
  conjuncts share nothing and the join is the independent existence check they always
  were, while a quantified one shares its binder and takes one witness for all of them."
  [kb unk bindings pctx]
  (provers/exception-holds? kb (sx/naf-query-conjuncts unk) bindings pctx))

(defn naf-blocks?
  "Is a firing blocked by any of its `unknown` antecedents `naf-antes` — is any inner
  query derivable under `bindings`, in `pctx`?  Block-if-**any**: each `(unknown S)`
  independently requires `S` absent, so one derivable `S` withdraws the conclusion."
  [kb naf-antes bindings pctx]
  (boolean (some #(unknown-inner-holds? kb % bindings pctx) naf-antes)))

(defn different-blocks?
  "Is a firing blocked because one of its `(different …)` antecedents no longer holds
  under `bindings`?  Block-if-**any**, for `naf-blocks?`' reason: each one independently
  requires its arguments to lie in no shared equivalence class and neither of them to be
  an unpinned `indeterminate_term`, so one that stops holding withdraws the conclusion.

  A justification cannot express this.  `different` is negation as failure over the
  equality closure and over the `indeterminate_term` category, so it holds by the
  *absence* of a merge and names no fact a firing's antecedents could carry — the
  `SupportingProver` contract has nothing to report, and `different` is not assertible
  (`wff/different-problems`), so no handle for it exists to name.  The re-check index is
  therefore the only instrument that can withdraw such a firing, and this is where it
  reads (docs/predall.md, `rules/different-flip-predicates`).

  `bindings` are the **settled** ones, so an argument the equality closure has since
  merged arrives here as its representative and the test fails on the `=` arm.  The goal
  goes to the registry under `?ctx`, which is the context `solve-deferred` joins it under:
  the two decisions have to read the literal the same way, or a firing would be placed and
  blocked in the same settle."
  [kb different-antes bindings]
  (boolean
   (some #(empty? (provers/solve-goal kb (res/substitute % bindings) '?ctx))
         different-antes)))

(defn closed-extent-antecedents
  "The rule's negative antecedents a `closed_extent_predicate` grant turns into negation as
  failure — closed (every variable bound by a generator) and declared closed somewhere.
  The join withholds these and derive time decides them, exactly as it does an `unknown`.

  One set read for a KB that declares no closed extent, which is the common one."
  [kb antes]
  (rules/closed-extent-antecedents (reasoning/taxonomy kb) antes))

(defn closed-extent-blocks?
  "Is a firing blocked because one of its withheld negative antecedents does **not** hold
  in `pctx`?

  The question asked is the whole level-6 one, not \"is there a positive answer\": a
  stored `(not (P a))` answers it as it always did, and under a visible grant
  `ClosedExtentProver` answers it from the absence of a positive.  So a placement context
  that cannot see the grant reads the literal exactly as it does today, and the
  withholding costs it only the support handle — which the re-check index gives back, by
  bringing the firing round again when anything on `P` moves.

  Block-if-**any**, like `unknown`: each withheld literal independently has to hold."
  [kb ce-antes bindings pctx]
  (boolean (some #(not (provers/exception-holds? kb [%] bindings pctx)) ce-antes)))

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
  earlier ones produced: an aggregate in `pctx`, any other literal in the wildcard, the
  context `solve-deferred` gives it in the join.

  Nil is a **block**: a literal has no answer, its already-bound output no longer
  matches the recomputed value, or its solutions disagree, which is also filed as
  `:post-join-ambiguous` with the solutions in content order.  At most two solutions are
  realized (docs/aggregate.md, \"Comparing the count\")."
  [kb literals bindings pctx]
  (reduce (fn [bs lit]
            (let [g    (res/substitute lit bs)
                  ctx  (if (sx/aggregate? lit) pctx '?ctx)
                  sols (into [] (comp (distinct) (take 2)) (provers/solve-goal kb g ctx))]
              (case (count sols)
                1 (merge bs (first sols))
                0 (reduced nil)
                (do (violations/report-once
                     kb {:violation :post-join-ambiguous
                         :context   pctx
                         :detail    {:literal   g
                                     :solutions (disagreeing-solutions sols)
                                     ;; `print-key`, not `pr-str`: the message is part of
                                     ;; what `report-once` dedupes on, and an ambient
                                     ;; `*print-length*` would elide two literals to one
                                     ;; string — or one literal to two, across a rebind
                                     :message   (str "post-join literal " (nm/print-key g)
                                                     " has more than one solution; a firing "
                                                     "that took one of them would depend on "
                                                     "the order the facts arrived")}})
                    (reduced nil)))))
          bindings
          literals))

(defn- rule-calculi
  "The registered calculi a rule's antecedents draw on — empty for every rule that does
  not mention one, and for every KB that registered no prover."
  [kb rsx]
  (into #{}
        (keep (fn [ante]
                (when (and (sequential? ante) (= 3 (count ante)) (symbol? (first ante)))
                  (qkb/calculus-for kb (first ante)))))
        (:antecedent rsx)))

(defn- entailment-withdrawn?
  "Was this firing licensed by a qualitative entailment the network no longer makes?

  Only one thing can do that, and it is worth being precise about which: adding a
  constraint only ever *narrows* what is possible, and narrowing makes a positive
  entailment more likely rather than less — so an entailed relation is never lost by
  learning more. The right to use it is what is lost at all, when the facts turn out to
  be unsatisfiable: an impossible theory entails everything and is mined for nothing.

  A justification's antecedents cannot express that. They name the facts the entailment
  rested on, and those are all still stored and believed when some *other* fact makes
  the network impossible. So the conclusion is blocked the way an excepted one is, and
  revived by the same machinery when the clash is retracted."
  [kb rsx pctx]
  (let [calcs (rule-calculi kb rsx)]
    (boolean (and (seq calcs)
                  (some #(qkb/inconsistent? % kb pctx) calcs)))))

(defn entailment-withdrawable?
  "Can `entailment-withdrawn?` answer true for any firing of the rule `rsx`, whatever
  context it was placed in?  Only while a calculus it joins on is unsatisfiable
  somewhere (`qkb/unsatisfiable-somewhere?`).  False lets a settle skip every firing of
  the rule its blocked set does not already hold."
  [kb rsx]
  (boolean (some #(qkb/unsatisfiable-somewhere? % kb) (rule-calculi kb rsx))))

(defn answered-by-calculus?
  "Can a registered calculus answer a goal on `pred` — `pred` or a sub-predicate of it is
  one a calculus claims?  Such a goal's answer moves with the whole network rather than
  with the facts on its own arguments.  The global closure, as a re-check trigger reads
  it: a sub-predicate any context sees can answer there."
  [kb pred]
  (boolean (and (symbol? pred)
                (some #(qkb/calculus-for kb %)
                      (tax/specs-global (reasoning/taxonomy kb) pred)))))

(def ^:dynamic *declarations-cell*
  "Per-run cache of `inherit/declarations-exist?` — whether the KB declares any
  preservation at all — as a volatile holding the answer, or nil (unknown, read on the
  next ask); the var itself is nil outside a chaining run, where the gate reads the
  index.

  `preserving-antecedent?` is asked of every non-trigger antecedent of every firing
  attempt, and its first question is this one: two cardinality reads that answer false
  for nearly every KB there is.  It is the only reader that caches it:
  `inherit/rejoin-rules` asks it live, each call.
  Bound once by `chain`, like `*evaluatable-preds*`, and unlike it **invalidated** from
  inside the run: a run can *derive* a declaration, and every join after that placement
  must see it — the re-join the placing datum queues (`inherit/rejoin-rules`) and a
  datum arriving later both match antecedents through `preserving-antecedent?`.
  `derive-conclusion` resets the cache when a placed conclusion **roots** at a
  declaration functor (`placed-functor`, since the conclusion the join hands over may
  still be wearing a `not`), so the next ask pays the two reads once more and caches
  the true.  A declaration leaves only outside a run (`retract!`), so a cached true
  never goes stale inside one."
  nil)

(def ^:dynamic *closure-rejoins*
  "Per-run record of the closure re-joins `fire-rules-for` has run, as a
  `java.util.HashMap` from rule handle to the `special/taxonomy-generations` stamp its
  full join read; nil outside a chaining run, where every closure edge re-joins in full.
  A rule whose stamp has not moved fires at the datum's trigger position instead
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
  cached answer to whether any exist, so the next join asks again.

  Asked of every firing that reached placement, whether or not it minted a handle: a
  conclusion that dedups onto a stored sentex places a *justification*, which is what
  makes the declaration believed, so \"nothing new was created\" is not \"nothing
  changed\".  Only a cached **false** can go stale — a declaration leaves only outside a
  run (`retract!`) — so a run that has not yet answered the question, or has answered it
  yes, skips the scan."
  [conjuncts]
  (when-let [v *declarations-cell*]
    (when (and (false? @v)
               (some #(contains? inherit/declarations (placed-functor %)) conjuncts))
      (vreset! v nil))))

(defn- preserving-antecedent?
  "Does `ante` name a predicate carrying a preserved argument position, visible from
  `context`?  False for every literal in a KB that declares no preservation, at the
  cost of the gate in front of `inherit/positions` — read once per chaining run
  (`*declarations-cell*`, re-read after a derived declaration), so the per-antecedent
  cost there is a var deref and a symbol test.

  A negation is not one: preservation licenses claims and never refutations, which is
  the same line `inherit/ground-goal?` draws."
  [kb ante context]
  (and (sequential? ante) (seq ante)
       (let [f (nm/functor ante)]
         (and (symbol? f) (not= 'not f) (seq (nm/args ante))
              (declarations-exist? kb)
              (boolean (seq (inherit/positions kb f context)))))))

(defn- inheritance-withdrawn?
  "Was this firing licensed by an inherited claim the KB no longer licenses?

  A justification's antecedents cannot express that.  They name the claim that was
  stated, the declaration that licensed the move and the relation edges the reach
  travelled — and every one of them is still stored and believed when a **more specific
  contrary claim** arrives and undercuts what they licensed.  Nothing is defeated
  there: the general claim simply stops firing for that tuple (docs/inherit.md), so
  there is no label to read the withdrawal off.  The firing is blocked the way an
  excepted one is, and revived by the same machinery when the specific claim goes.

  Asked only of an antecedent the KB does **not** state at the bound tuple.  A stored
  claim is withdrawn by its own handle going, and asking `verdict` about one would
  block an ordinary firing over a pair the KB happens to hold in both polarities —
  which is a represented dilemma the chainer has never refused to fire on.

  In the conclusion's context, like every other re-check here: a specific claim that
  context cannot see is not one it should defer to, and everything the firing rests on
  is visible from there by construction, placement having required it.  The claims are
  read in the network and through the excepts, and no placed defeat is read
  (`tax/*network-belief*`), so a defeated specific claim still undercuts (design ruling
  19).

  `bindings` is a delay, forced only once a preserved antecedent is found — every rule
  reaches here and almost none names one."
  [kb rsx bindings pctx]
  (let [as (filterv #(preserving-antecedent? kb % pctx) (:antecedent rsx))]
    (boolean
     (and (seq as)
          (binding [tax/*network-belief* true
                    inherit/*memo*       nil]
            (some (fn [a]
                    (let [g (res/substitute a @bindings)]
                      (and (inherit/ground-goal? g)
                           (not-any? #(jtms/in? (reasoning/tms kb) (first %))
                                     (res/matches-visible kb g pctx))
                           (not= :for (inherit/verdict kb g pctx)))))
                  as))))))

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
  "A firing's stored bindings, with each bound term rewritten to the representative
  `pctx` now elects.

  A justification records what matched **when it fired**, and an equality merge does not
  go back and edit it: a firing that bound `?c` to `C3` still says `C3` after `(sameAs
  C2 C3)` has retired that spelling.  Every re-check below substitutes these bindings
  into a query and asks the engine — so left as stored they ask about a term the KB no
  longer answers under, and what comes back is an empty result that reads as *not
  excepted*, *not derivable*, *counted nothing*.  An `exceptWhen` would quietly stop
  guarding, which is the loudest way this can go wrong: an unanswerable exception does
  not hold, and the rule fires.

  Rewritten in the **conclusion's** context, the scoping every other read of the
  partition takes — a merge that context cannot see must not rename what its own
  re-check asks about.  One visibility predicate for the whole map, since a firing's
  bindings are all read from the one context and building it costs a record fetch per
  equality supporter.

  A KB whose partition is empty and which declares no schematic equation hands the
  bindings straight back — the two things that could rewrite a term are the two gated
  here, and this runs per firing on the settle path, where a `filterv` over the rewrite
  rules per bound term is what an ungated version would cost."
  [kb bindings pctx]
  (let [tx (reasoning/taxonomy kb)]
    (if (and (nil? (tax/merged-term-pred tx)) (empty? (tax/rewrite-rules tx)))
      bindings
      (let [visible? (res/visible-supporter-fn kb pctx)]
        (reduce-kv (fn [m v t] (assoc m v (kb/rewrite-term* kb t visible?))) {} bindings)))))

(defn- antecedent-hidden?
  "Does a believed visibility `except` hide one of `antes` from `pctx`: name it, or name a
  handle every justification route of it rests on (`exc/except-closure-hidden-fn`, the
  reading a placement takes)?  A derivation resting on an antecedent the conclusion's
  context cannot see is invalid there.

  Asked per antecedent rather than against a materialized hidden set, because this runs
  once per placement and once per candidate justification.  A nil predicate is the gate:
  a KB that states no except where `pctx` sees pays a deref and returns here.  The rule
  handle among `antes` is asked too: a rule is a sentex and an `except` may target it, and
  a firing rests on its rule as it rests on its facts (`special/recheck-except` carries
  the departure-side twin)."
  [kb antes pctx]
  (if-let [hidden? (exc/except-closure-hidden-fn kb pctx)]
    (boolean (some hidden? antes))
    false))

(defn- rule-firing-blocked?
  "Is a firing of the rule stored at `rh` — settled bindings `bindings` (a delay),
  placed in `pctx` — blocked by something the *rule* carries: its `exceptWhen`
  exception, an `(unknown S)` antecedent whose `S` is now derivable, a `(different …)`
  antecedent a merge or an indeterminacy has since withdrawn, a **closed-extent**
  negative antecedent that no longer holds, an **aggregate** antecedent whose count has
  moved, an **inherited** antecedent a more specific claim has undercut, or the
  qualitative network it joined on having become unsatisfiable?

  The context is the **conclusion's**, not the rule's: an exceptWhen query and a NAF
  literal are *about* the conclusion, and one invisible from where it lives has no
  business blocking it.  Nothing is cached: this re-runs the checks every time, which is
  what keeps blocking from drifting out of step with belief.

  Both re-decision paths come here — a firing that *was* placed and is now a
  justification, and one that was refused before it could become one — so the two cannot
  drift about what counts as blocked."
  [kb rh rsx bindings pctx]
  (boolean
   (or (when (or (rules/has-naf? rsx) (reads/watched-rule? (:index kb) rh))
         (or (provers/exceptions-block? kb rh @bindings pctx)
             (and (rules/has-naf? rsx)
                  (naf-blocks? kb (rules/naf-antecedents rsx) @bindings pctx))))
       (when (rules/has-different? rsx)
         (different-blocks? kb (rules/different-antecedents rsx) @bindings))
       (when-let [ce (seq (closed-extent-antecedents kb (:antecedent rsx)))]
         (closed-extent-blocks? kb ce @bindings pctx))
       (post-join-withdrawn? kb rsx bindings pctx)
       (inheritance-withdrawn? kb rsx bindings pctx)
       (entailment-withdrawn? kb rsx pctx))))

(defn justification-excepted?
  "Is justification `j` currently blocked — by a visibility `except` hiding one of its
  antecedents, or by anything its rule carries (`rule-firing-blocked?`)?

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
           (when (integer? inf)
             (when-let [rsx (p/get-sentex (:records kb) inf)]
               (rule-firing-blocked? kb inf rsx
                                     (delay (settled-bindings kb (:bindings j) pctx))
                                     pctx))))))))

;; ---- forward chaining ---------------------------------------------------

;; **Deferred antecedents.**  A deferred (evaluable) literal — `lessThan`,
;; `greaterThan`, `evaluate`, `different` (`sentex/deferred-predicates`), and a
;; predicate the KB registered with `add-evaluatable` (`deferred-antecedent?`) — is not
;; a stored fact.  It is *computed* from the bindings the other antecedents produced,
;; which is why `vaelii.impl.sentex` holds a built-in back to the end of the canonical
;; antecedent order and `vaelii.impl.plan` pulls it forward only once its inputs are
;; bound.  Joining it with `match-pattern` therefore looks up a fact nobody ever
;; stored, finds nothing, and kills the whole join — silently, since an empty join is
;; indistinguishable from a rule that simply had nothing to fire on.  The backward
;; chainers never had that bug because they discharge every antecedent through
;; `provers/solve-goal`, where the evaluable provers live.  The join below goes to the
;; same registry rather than growing a second evaluator that could disagree with it.
;;
;; A **registered evaluatable** takes the same path, so `ask` agrees with `query` on a
;; forward rule with an evaluatable antecedent.  It differs from a built-in in one
;; respect: it is per-KB, so it is not in the static `deferred-predicates` set the
;; canonical order pins on, and `planned-join` pins it after its binders by cost instead
;; (`provers/evaluatable-est-override`) — which is what keeps the firing order-independent
;; whether the facts or the rule arrive first.

(defn- solve-deferred
  "Solve a deferred antecedent against `bindings` by **computing** it: the substituted
  literal goes to the prover registry, which answers it with `EvaluableProver` /
  `EvaluateProver` / `DifferentProver` / `QuantityProver`.  Returns `[bindings support]`
  pairs — a test (`lessThan`, `different`) yields the bindings unchanged or nothing at
  all, while `evaluate` adds the binding it computed, so both the testing and the binding
  flavour fall out of the one call.

  **`support` is the handles the answer was read from**, and it is what a computed
  antecedent contributes to the firing's justification.  Empty for the arithmetic
  comparisons, whose answer is a function of the bindings in front of them and of nothing
  stored — `(lessThan 3 5)` names no fact and no retraction can un-hold it.  Not empty for
  a prover whose answer moves with the store: a measure comparison normalizes both sides
  through the KB's `dimensionOf` / `conversionFactor` table, so `(quantityLessThan
  (QuantityFn 500 Gram) (QuantityFn 1 Kilogram))` holds *because* a gram is declared a
  thousandth of a kilogram, and a conclusion drawn from it has to go when that
  declaration does.  Which provers can say this is `prover-types/SupportingProver`; the ones
  that cannot report empty, and the protocol is what makes that the defensible answer rather than
  merely the convenient one.

  The context is the wildcard, and deliberately so: a computed literal holds wherever its
  inputs do, so the join asks the registry the same context-free question it asks the
  matcher.  Where the answer *did* rest on stored knowledge, the handles above say which,
  and placement then reads their contexts exactly as it reads a matched fact's — so a
  conclusion may only be placed where the declarations behind it can be seen.

  **Its inputs must already be bound**, and two things arrange that before the join
  runs: `sentex/check-naf-closed` refuses at assert time a rule whose deferred literal
  reads a variable nothing in the rule writes, and `planned-join` withholds the ones
  whose inputs an aggregate supplies per placement.  So reaching here unbound means one
  of those two broke, and it throws.  Answering it with an empty join instead would
  report a comparison that was never *run* as a comparison that *failed*, which is
  precisely the silent-empty-join failure this whole section exists to remove."
  [kb literal bindings]
  (let [g (res/substitute literal bindings)]
    ;; The unbound-input guard is for the built-in deferred literals, whose input/output
    ;; split `sentex/deferred-input-vars` knows statically.  A KB evaluatable's output
    ;; slot is the prover's (`add-evaluatable`'s `:result`), which is not in that map, so
    ;; a result-binding evaluatable's own output would read here as an unbound *input* and
    ;; throw spuriously.  Its readiness is left to the prover instead — `EvaluatableFn`
    ;; yields nothing until its inputs are ground — and `planned-join`'s `est-override`
    ;; orders it after their binders so it lands ground.
    (when (sx/deferred-literal? literal)
      (when-let [unbound (seq (sx/deferred-input-vars g))]
        (throw (ex-info (str "deferred antecedent " (pr-str g) " reached the join with unbound "
                             "input " (pr-str (vec unbound)) " — it is computed, not looked up, "
                             "so an earlier antecedent must bind its inputs")
                        {:type :unbound-deferred :literal literal :goal g :unbound (vec unbound)}))))
    (map (fn [[b sup]] [(merge bindings b) sup])
         (provers/solve-goal-with-support kb g '?ctx))))

;; ---- qualitative antecedents: joining on what a network entails ----------
;; A relation algebra derives relations nobody stored (docs/qcn.md).  Those could not
;; fire a forward rule, and the reason was not the wiring: an entailed relation has no
;; handle, so there was no antecedent for a justification to rest on, and a conclusion
;; nothing can withdraw is worse than a conclusion never drawn.
;;
;; Support closes it.  The fixpoint now reports which stored facts a tightened
;; constraint rests on, so an entailed antecedent contributes *those* handles — the
;; conclusion is withdrawn when any fact behind the entailment goes, which is exactly
;; the contract an ordinary matched antecedent has.  The **arithmetic** half of the
;; deferred path has nothing to report and correctly reports nothing: `(lessThan 1 2)` is
;; a function of the bindings, where `(partOfRegion A C)` is a function of what is
;; *stored*.  Which half a deferred literal falls in is not the join's guess —
;; `prover-types/SupportingProver` is where a prover says so, and a measure comparison, whose
;; answer moves with the unit table, is in the same business as this section.
;;
;; This is **union, not replacement**.  Entailment subsumes assertion — an asserted
;; relation is trivially entailed — but the two disagree at the edges (a literal whose
;; arguments are not network nodes is outside the calculus under either polarity), so
;; the ordinary matcher still runs and nothing that matched before stops matching.
;; Duplicate justifications from the two routes are set-deduped by the TMS.

(def ^:dynamic *qcn-contexts*
  "Per-run cache of `{calculus-name -> #{context}}` — the readers of a calculus, which
  are the networks an entailed antecedent is solved against.

  Collecting them walks the calculus's own extent, the same order as reading one
  network, and where its facts span contexts a `genlCx` closure besides, so it
  is cached for the length of a chaining run rather than recomputed per antecedent per
  binding.  Bound by `chain`; nil outside one, where it simply recomputes."
  nil)

(defn- calculus-contexts
  "The networks worth re-joining `calc` against — `qcn-kb/reader-contexts`, cached for
  the length of a chaining run.

  A network is what a **reader** sees, and a reader sees the whole `genlCx` ancestor set
  above it, so the contexts that merely *hold* a fact are not the networks a forward
  rule may join on: a context inheriting two contexts composes what neither
  composes alone, and that entailment exists for no other reader.  `ask` has always
  answered it there.  Left at the fact contexts, such a firing would wait for some
  unrelated fact to be stated in the meeting context and then survive its retraction —
  belief decided by an assertion that entails nothing, which is the arrival-order
  dependence the engine does not allow (docs/nmtms.md).

  Which context the *conclusion* lands in is still not decided here.  Placement reads
  the contexts of the support handles, exactly as it reads the contexts of ordinarily
  matched facts, so a firing solved at a meeting context is placed by the facts that
  entailed it and lands there because *they* meet there."
  [kb calc]
  (if-let [memo *qcn-contexts*]
    (or (get @memo (:name calc))
        (let [cs (qkb/reader-contexts kb calc)] (swap! memo assoc (:name calc) cs) cs))
    (qkb/reader-contexts kb calc)))

(def ^:dynamic *qualitative-delta*
  "`{:literal <antecedent> :moved {context (:all | #{pair})}}`, or nil.

  What makes a re-join **semi-naive**.  A qualitative fact re-joins every rule mentioning
  its calculus, and joining over every pair the network entails means the nth arriving
  fact redoes what the (n-1)th already did.  Bound by `rejoin-qualitative` to the pairs
  that have moved since the last such re-join (`qcn-kb/join-delta`), it narrows the
  enumeration of **one** antecedent — the named literal — and leaves the rest full.

  One antecedent, because that is the delta rule: for a rule with two qualitative
  antecedents, narrowing both at once would drop every firing pairing a moved binding with
  an unmoved one.  So `rejoin-qualitative` runs the join once per qualitative antecedent,
  each with a different one narrowed, and the overlap re-derives conclusions the TMS
  dedups.

  Read by literal rather than by position: `plan/order` reorders the antecedents, so a
  position means nothing by the time the join runs.  Two identical antecedents in one rule
  are both narrowed, which is the same set — they bind identically."
  nil)

(defn- solve-qualitative
  "Solve a qualitative antecedent by **entailment**, against every network the calculus
  has facts in.  Each solution carries the support handles the entailment rests on, so
  the firing's justification names them and retraction reaches them.

  An entailment with empty support is dropped by `qcn-kb/solve-with-support` rather than
  answered groundlessly — see there.

  Narrowed to the moved pairs when this is the literal `*qualitative-delta*` names, and a
  context nothing moved in is skipped outright.  Both are per **context**: an arriving
  fact narrows the networks that see it and leaves the others exactly where they were."
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
  "The registered calculus claiming `ante`, or nil — nil for every KB that registered no
  prover.  Nil is close to free: `qkb/calculus-for` memoizes the registered-calculus
  list against the registry vector, so a repeat registry costs a volatile read and an
  identity compare, and the per-prover `instance?` scan runs only when the registry
  itself changed.  The shape gate in front of it is still the larger saving, and it is
  arity-only: positive binary literals, a negated one being refuted by the network rather
  than entailed by it, and what a refutation rests on is the whole network rather than a
  support list."
  [kb ante]
  (when (and (sequential? ante) (= 3 (count ante)) (symbol? (first ante)))
    (qkb/calculus-for kb (first ante))))

;; ---- inherited antecedents: joining on a claim nobody stored -------------
;; `(transitiveInArg P n R)` makes a stored `(P … W …)` license `(P … A …)` for every A
;; in W's reach (docs/inherit.md).  Backward chaining discharges such an antecedent
;; through `TransitiveInArgProver`; forward chaining could not, and the reason was the
;; qualitative one — an inherited claim is not stored, so it has no handle for a
;; justification to rest on, and `sentexes-matching` and `ask` came back with different
;; answers about the same knowledge.
;;
;; Support closes it here too.  `inherit/solve-with-support` answers the antecedent by
;; the reach and hands back the handles the claim was **read from** — the claim that
;; was stated, the declaration licensing the move, and the relation edges the reach
;; travelled — so the conclusion is withdrawn when any of them goes, `why` names the
;; actual reasons, and the conclusion may only be placed where they can all be seen.
;;
;; **Union, not replacement**, and for the same reason it is on the qualitative side: a
;; stored claim keeps matching exactly as it does now, the inherited ones are added,
;; and the diagonal — a claim stated at the very tuple it is asked about — is dropped
;; from this path rather than handed a second justification resting on nothing new.

(defn- solve-preserving
  "Solve an antecedent by **preservation**, against the claims stored anywhere.  Each
  solution carries the handles the inherited claim rests on, so the firing's
  justification names them and retraction reaches them.

  The context is `'?ctx` throughout, exactly as the ordinary matcher's is: which claims
  exist is not the placement's question, and the reasons this hands back are what
  placement then reads to decide where the conclusion may live."
  [kb literal states]
  (let [ak (rules/antecedent-key literal)]
    (for [{:keys [bindings handles matched]} states
          :let [g (res/substitute literal bindings)]
          {b :bindings sup :handles claim :claim} (inherit/solve-with-support
                                                   kb g '?ctx)]
      ;; the claim satisfied the antecedent like any other match, and it may have done
      ;; so through a sub-predicate — so it is paired with the antecedent's key and
      ;; `subsumption-links` reads the taxonomy edges *that* pairing rests on.  The
      ;; declaration and the reach edges are not paired: they are what licensed the
      ;; move, not facts that matched a pattern.
      {:bindings (merge bindings b) :handles (into handles sup)
       :matched  (conj matched [ak claim])})))

;; ---- computed antecedents: joining on what a prover reads out of the store -----
;; A `SupportingProver` answers a goal from stored facts nothing about the goal names —
;; the metric closure over every `temporalDistance` in the network, the `length` rows a
;; duration sums.  Backward chaining discharges such an antecedent through
;; `provers/solve-goal`; forward chaining could not, and the reason was the qualitative
;; and the inherited one over again: a computed answer has no handle, so there was no
;; antecedent for a justification to rest on, and `ask` and forward chaining came back
;; with different answers about the same rule.
;;
;; Support closes it here too, and the `SupportingProver` protocol is what makes it possible: the prover reports
;; the handles the answer was read from, so the firing rests on exactly the facts behind
;; the computation and the ordinary relabel withdraws it when any of them goes.
;;
;; **Per reader context**, unlike the deferred arm.  A metric network is what one reader
;; sees up its `genlCx` ancestor set, so a wildcard read would close one network out of every
;; context's constraints at once — a bound no reader entails.  `provers/source-contexts`
;; enumerates the readers, `qcn-kb/reader-contexts`' argument applied to a prover that is
;; not a calculus.
;;
;; **Union, not replacement**, for the reason it is on the other two sides: a
;; `temporalDistance` is a stored fact as well as a derived bound, so the ordinary matcher
;; still runs and nothing that matched before stops matching.  A stated constraint is on
;; its own shortest path, so the two routes agree about what supports it and the TMS
;; set-dedups the duplicate justification.

(defn- computed-antecedent?
  "Is `ante` a literal a registered `SupportingProver` answers — and therefore one the
  join solves by computation as well as by matching?

  Nil is close to free: `provers/support-answered-preds` memoizes against the registry's
  identity, so this is a set lookup on a functor.  It is not empty for the default
  registry — `QuantityProver` ships in it — so the gate below is a `contains?` on the
  literal's own functor and stops there for every ordinary antecedent."
  [kb ante]
  (and (sequential? ante) (seq ante) (symbol? (first ante))
       (contains? (provers/support-answered-preds kb) (first ante))))

(defn- solve-computed
  "Solve an antecedent by **computation over stored facts**, at each reader context the
  prover's sources reach.  Each solution carries the handles the answer rested on, so the
  firing's justification names them and retraction reaches them.

  An answer with **empty** support is dropped rather than answered groundlessly, exactly
  as an entailment with none is (`qcn-kb/solve-with-support`).  The metric diagonal is the
  case: `(temporalDistance P P ?d)` is nil by arithmetic, licensed by no constraint, and a
  conclusion drawn from it would rest on the rule alone while looking as though it rested
  on the network.

  `:matched` passes through unextended, for `solve-qualitative`'s reason: the answer was
  licensed by a computation over the store rather than by the taxonomy, so it rests on no
  `genl` edge and has no antecedent-functor pairing to record.

  `ctxs` are the contexts worth asking at, the readers of the facts the answer is read
  from (`provers/source-contexts`).  They default to those of the whole registry's
  declared sources, which is what a `SupportingProver` with a fixed roster wants; a
  transitive antecedent passes its own walk's instead (`transitive-contexts`), since what
  the walk reads is a taxonomy read rather than a constant."
  ([kb literal states]
   (solve-computed kb literal states
                   (provers/source-contexts kb (provers/support-source-preds kb))))
  ([kb literal states ctxs]
   (distinct
    (for [{:keys [bindings handles matched]} states
          :let [g (res/substitute literal bindings)]
          ctx ctxs
          [bnd sup] (provers/solve-goal-with-support kb g ctx)
          :when (seq sup)]
      {:bindings (merge bindings bnd) :handles (into handles sup) :matched matched}))))

;; ---- a transitive antecedent reads the closure, with the edges it crossed ----
;; An antecedent on a `(transitive P)` predicate is a fourth shape the join answers by
;; computation and not only by matching, beside the qualitative, the computed and the
;; preserving one — and it is the one whose roster is a taxonomy read: which predicates
;; `TransitivePredicateProver` answers is whatever *this* KB declared, so it cannot be a set
;; on the prover the way a unit table's predicates are (`prover-types/SupportingProver`, and the
;; empty rosters there).
;;
;; The join without it sees stored edges only, so `(implies (and (causes ?a ?c) …) …)`
;; fires across one hop and not across two, and a narrative has to write down every pair it
;; wants read rather than the links it actually recorded.  With it the closure's answers are
;; **unioned** with the matcher's — a stated edge is still a stated edge, and the two
;; routes agree about what supports it, so the TMS set-dedups the duplicate justification.
;;
;; Per reader context, as the metric arm is: a hop is visible or not from where it is
;; read, so a wildcard walk would cross an edge in a context that cannot see it.

(defn- walks-its-own-conclusion?
  "Does the rule being fired **conclude** on the walked predicate `pred` itself, or on a
  **sub-predicate** of it — a conclusion that becomes a `pred`-edge by genl subsumption,
  the graph the walk also reads?

  Such a rule is the closure written out, and the two must not both run.  A rule deriving
  `(P x z)` from `(P x y)` and `(P y z)` stores its conclusions *inside* the fixpoint, so a
  walk beside it would find a different shortest chain depending on how far the rule had
  got — two chainers agreeing about every belief would still record different antecedents
  for one conclusion.  Nothing is lost by declining: the rule reaches every pair the walk
  would, and stores each as a hop the matcher then matches directly.

  A property of the **rule**, so it is the same answer whatever else the KB holds and
  whatever order it arrived in — which a roster of \"predicates some rule concludes\" could
  not be, that set growing as rules land.  **One direction only.**  A rule concluding
  `pred` or a *sub*-predicate of it feeds that graph — a sub-predicate tuple is a `pred`
  tuple by subsumption — so it is the closure one level down and the walk must yield.  A
  rule concluding a *super*-predicate does not: a general conclusion is no fact about the
  specific `pred`, so its firing and the walk cannot disagree about `pred`'s chains, and
  suppressing the walk there would drop sound two-hop derivations for nothing.  So only
  `pred ∈ genls*(cpred)` (which is reflexive, catching the `pred = cpred` closure rule),
  never `pred ∈ specs*(cpred)`."
  [kb pred cpred]
  (let [tx (reasoning/taxonomy kb)]
    (boolean (and cpred (symbol? cpred)
                  (contains? (tax/genls-global tx cpred) pred)))))

(defn- transitive-antecedent?
  "Is `ante` a binary literal whose own functor this KB declares `(transitive P)` — and
  therefore one the join can solve by walking the stored edges as well as by matching?

  `genl` and `genlCx` are excluded, exactly as they are in the prover: their closures are
  cached relations answered by their own provers, and nothing about them is a walk over
  believed facts.  A rule that concludes on what it would walk is excluded too, and
  `walks-its-own-conclusion?` says why; `cpred` is the consequent predicate the join is
  running for, nil where there is none to read.

  One map read on a KB that declares no transitive predicate, which is where it stops for
  nearly every rule; the closure reads behind the recursion test are paid only for an
  antecedent on a predicate this KB actually declared transitive."
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
;; `TransitivityProver` answers a `genl` or `genlCx` goal from the cached closure, so a
;; query reads the reflexive pair and every pair more than one edge apart.  The matcher
;; reads the stored edges alone, so a forward join that ran only the matcher would
;; disagree with the query about the same literal.  The closure arm below unions the
;; closure's answers with the matcher's, as the transitive arm does for a walk.
;;
;; A closure answer names no stored tuple, so it records what it rests on another way.
;; A `genl` pair two terms apart is recorded as a **closure link** on `:matched`, a
;; `[key nil [sub super]]` entry, and `subsumption-links` hands it to placement beside the
;; links a subsumed match makes: the conclusion then lands where a `genl` path from `sub`
;; to `super` is visible, and its justification names the edges of that path.  A
;; `genlCx` pair names the edges of one path on `:handles`, the strongest by defeat class.
;; A reflexive pair rests on no edge and adds nothing.

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
  "Solve a `genl` / `genlCx` antecedent from the cached closure, per join state.

  **Bounded arms only.**  Both ends bound is a membership test; one end bound reads that
  end's closure, the reflexive member included, which is what `TransitivityProver`
  answers for the same goal.  Both ends open contributes nothing, and the stored edges the
  matcher returns answer alone: the closure over every pair is quadratic in the length of
  a chain, the reason the transitive arm gives (docs/taxonomy.md).  An open end that is a
  pattern rather than a variable contributes nothing either.

  The `genl` closure is read globally, as `subsumption-links` reads it: which pairs the
  closure relates is a property of the KB, and which contexts see a path between them is
  placement's question, asked through the closure link.  The `genlCx` closure is read
  from the lower context, as the prover reads it, and a pair whose path the witness view
  cannot see is dropped."
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

(defn- mirrored-antecedent?
  "Is `ante` a literal the matcher answers through the **symmetric mirror** — a binary
  literal any of whose sub-predicates is declared `symmetric` (`res/raw-match`)?

  Such a position takes no arrival filter, and the reason is an asymmetry between the
  two ways a rule reaches a fact.  The join runs `*matcher*`, which probes both
  argument orders; the trigger runs `res/match1`, which is a plain unify and does not.
  So `(siblingOf ?y ?z)` joined under `?y = I3` finds the stored `(siblingOf I2 I3)`
  by its mirror, while that same fact arriving as a datum unifies only as
  `?y = I2, ?z = I3` and reaches a different firing.  Suppressing the join hit would
  hand the pair to a trigger that cannot make it.

  The sub-predicate closure rather than the functor alone, because `match-pattern`
  fans the functor first and mirrors each fanned literal on **its** own declaration.
  Driven from the declared symmetric predicates (a handful) tested against the closure,
  as `matches-hierarchical` does, rather than the closure scanned for a mark: a broad
  functor's closure is the whole type hierarchy, and this runs per join."
  [kb ante]
  (and (sequential? ante) (= 3 (count ante))
       (let [f (nm/functor ante)]
         (and (symbol? f) (not (sx/variable? f))
              (let [tx    (reasoning/taxonomy kb)
                    specs (res/sub-predicates kb f nil)]
                (boolean (some #(contains? specs %) (tax/props tx :symmetric))))))))

(defn- permuting-antecedent?
  "Could the matcher answer `ante` from a stored fact read in an order other than the one
  it is stored in — a positive literal any of whose sub-predicates carries `symmetric` (at
  two arguments) or a commutativity group?  The gate on `read-marks`, asked once per
  antecedent per join, so a KB with no permuting mark pays two empty-table reads.

  Wider than `mirrored-antecedent?`, which decides the arrival filter and asks only for
  `symmetric`: the trigger fans a commuting antecedent's arrangements itself
  (`trigger-bindings`), so a commuting position keeps its filter, while either one names
  the mark it was read through."
  [kb ante]
  (and (sequential? ante) (next ante)
       (let [f (nm/functor ante)]
         (and (symbol? f) (not (sx/variable? f)) (not= sx/not-functor f)
              (let [tx   (reasoning/taxonomy kb)
                    syms (tax/props tx :symmetric)]
                (and (or (seq syms) (tax/commuting-declared? tx))
                     (let [specs (res/sub-predicates kb f nil)]
                       (boolean (or (and (= 3 (count ante)) (some #(contains? specs %) syms))
                                    (tax/commuting-predicates-among tx specs))))))))))

(defn- read-marks
  "The alternative sets of mark handles a match of `pattern` under `b` rests on, when the
  stored fact at `h` was read in another argument order (`inherit/permuted-read-supports`),
  else `[[]]` — one firing naming nothing more, as every unpermuted match is."
  [kb pattern b h stored]
  (let [sxr (if (:sentence stored) stored (p/get-sentex (:records kb) h))
        sen (:sentence sxr)]
    (or (when (sequential? sen)
          (inherit/permuted-read-supports kb sen
                                          (vec (rest (res/substitute pattern b)))
                                          '?ctx))
        [[]])))

(defn- symmetric-mirror
  "The mirror of `fact` when the KB reads it as one — a binary literal whose own
  predicate is declared `symmetric`, and whose arguments differ — else nil.

  A symmetric fact is stored in one orientation (the canonical sort) and *means* both,
  which is why `res/raw-match` probes both when a join reaches it.  A trigger reaches it
  the other way round: the fact arrives and `res/match1` unifies it as written, so the
  combination that needs the mirror is enumerated by nobody, and the same two facts
  derive a conclusion or not depending on which arrived second.  Asked of the **fact**
  and once per datum: it is the fact's own declaration that makes its mirror true, and a
  super-predicate being symmetric says nothing about the sub the fact is stated at."
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
  asks the same fact."
  [kb fact]
  (when (and (sequential? fact) (next fact))
    (let [f (nm/functor fact)]
      (when (and (symbol? f) (not (sx/variable? f)))
        (sx/commuting-components (tax/commuting-groups (reasoning/taxonomy kb) f)
                                 (dec (count fact)))))))

(defn- trigger-bindings
  "The binding maps a datum makes at one antecedent position: what `fact` unifies to,
  what its symmetric `mirror` unifies to, and what each **arrangement of the antecedent**
  under `comps` unifies to — each kept when it binds differently.

  More than one is what keeps a permuting antecedent at the *trigger* position reading the
  same as it does at a join position, and with it the run's independence from arrival
  order.  The join runs `*matcher*`, which fans the arrangements; the trigger runs
  `res/match1`, a plain unify that does not — so `(covering ?w C A B)` joined finds the
  stored `(covering W A B C)`, while that same fact arriving as a datum unifies against
  the antecedent as written and reaches no firing at all.

  **The antecedent is what is rearranged, not the fact.**  A stored fact is canonical
  already (`sentex/sort-commuting-args`), so its own permutations are not what is missing;
  what is missing is the antecedent spelled the way the fact holds it.  Rearranging the
  pattern is also what keeps the fan pruned — `sentex/arrangements-over` drops an
  arrangement whose ground arguments are out of order, which is exactly the set a
  canonical fact cannot match.  The binary `mirror` stays as it was: at two positions the
  fact's mirror and the antecedent's are the same swap, and that path is what the
  symmetric rows pin.

  Distinct, because an antecedent that binds two arrangements the same way (a repeated
  variable, or a position the arrangement does not move) has made one firing, not two —
  and a duplicate would be a second justification for a conclusion the first already
  carries."
  [kb ante fact mirror comps]
  (let [b0   (res/match1 kb ante fact)
        b1   (when mirror (res/match1 kb ante mirror))
        alts (when comps
               (keep #(res/match1 kb % fact) (rest (sx/arrangements-over ante comps))))]
    (not-empty (into [] (comp (remove nil?) (distinct)) (concat [b0 b1] alts)))))

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
  "Is `ante` a **computed** antecedent for `kb` — a built-in evaluable
  (`sentex/deferred-predicates`) or a predicate the KB registered with
  `add-evaluatable`?  Forward chaining discharges these through the prover registry
  (`solve-deferred`) rather than looking them up with `*matcher*`, so `ask` reaches the
  same evaluatable the query engine's leaf does and the two agree on a rule with an
  evaluatable antecedent.

  A registered evaluatable is *not* in canonical antecedent order's deferred set (that
  set is static, evaluatables are per-KB), so `planned-join` instead pins it after its
  binders with `provers/evaluatable-est-override` — which is why the ordering holds
  regardless of assertion order.

  Called per antecedent on the join hot path, so the registered-evaluatable arm is gated
  on a non-empty predicate set first: the common KB registers none, so this collapses to
  the built-in `sx/deferred-literal?` check with only a set-empty test added."
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
        (> (count (res/sub-predicates kb f '?ctx)) 1))))

(defn- join-matches
  "The stored facts satisfying the substituted antecedent `g` at the wildcard context —
  `[handle bindings …]` pairs, the set `res/match-pattern` returns.

  Two readers answer the same question, and the choice between them is the one the
  query side already makes (`res/matches-visible`).  `*matcher*` is the reference: the
  count-aware trie, one walk per member of the functor's sub-predicate closure, and the
  extension point the rete alpha matcher binds.  For a literal with a **bound indexable argument**
  — a type test `(animal ?x)` with `?x` already bound, the commonest non-trigger
  antecedent there is — that fan is `|specs|` trie walks to confirm one membership (364
  for `animal` on the starter, six figures under a `thing`-rooted antecedent on a large
  KB) per firing attempt, where `res/matches-hierarchical` leads from the argument's
  own postings: one slot-roster read kept to the closure, then the kept predicates' nodes,
  or one scoped read per spec when that side is smaller (`res/*lead-side*`).  Same belief
  filter, same polarity check, same symmetric mirror, same exceptWhen-meta skip, and the
  same `?ctx` binding — `matches_hierarchical_test` holds the two to the identical set.

  **The lead is for the fan, so a functor with no sub-predicates keeps the trie.**  A
  singleton closure is `match-pattern`'s own fast path — one cached set lookup and a
  single `raw-match`, whose `candidate-handles` already reads the argument roots for the
  shape the trie cannot narrow (a ground argument behind a variable) and the trie for the
  shapes it can.  There is no `|specs|` fan there to collapse, and the lead is not free:
  three volatiles, a pattern memo, two `prof/profiling?` derefs and `lead-agnostic?`'s
  own `count-with-arg` probe.  Measured over 2,000 firings of a binary join on `:memory`,
  the same 2,000 conclusions: 52,003 index reads through the lead against 48,003 through
  the trie, and the whole difference is the argument families.  `fanning-functor?` is the
  gate, and `join_lead_cost_test` measures at width 0 as well as at 4 and 16 so a lead
  taken over nothing fails there.

  The lead is taken only when the reference matcher is the one bound: a rete run keeps
  its protocol, and `res/*hierarchical-retrieval*` false (the reference-retrieval sweep)
  keeps the trie everywhere, so the join is the reference under exactly the bindings
  the rest of the engine is."
  [kb g]
  (if (and res/*hierarchical-retrieval*
           (identical? *matcher* res/match-pattern)
           (res/lead-literal? g)
           (fanning-functor? kb g))
    (res/matches-hierarchical kb g '?ctx)
    (*matcher* kb g '?ctx)))

(defn- join-antecedent
  "Extend the partial join `states` ({:bindings :handles :matched}) by one antecedent.

  `admit` is the arrival filter on the handles this antecedent yields — a
  `(fn [handle] -> boolean)` from `complete-antecedents`, or nil for no suppression
  (`*agenda-arrivals*`).  **Five** positions decline it, and the rule is the same one
  each time: the join reaches a satisfier no trigger can, so there is nothing to order
  it against.  A **qualitative** antecedent draws its handles from what a network
  entails rather than from the fact that satisfied it; a **computed** one draws them from
  what a prover read out of the store rather than from a tuple; an **inherited** one is
  satisfied by a claim nobody stored, whose handles name the stated claim, the
  declaration and the reach edges rather than the tuple that matched; a **closure** one
  is satisfied by a `genl` / `genlCx` pair no edge states (`solve-closure`); and a
  **mirrored** one is reachable by the join and not by the trigger
  (`mirrored-antecedent?`).  The first four decline it structurally — the filter is
  applied to `hit` alone, and each arrives by its own `concat`.  Declining is always
  safe — it re-derives a duplicate the TMS already rejects — where suppressing wrongly
  loses a firing.

  A computed literal contributes **the handles its answer was read from, and no more**.
  For the arithmetic comparisons that is nothing: `(lessThan ?a ?b)` is a function of the
  bindings, those bindings came from the fact handles already listed, and dropping any
  contributing fact still withdraws the conclusion — so a firing whose antecedents are all
  arithmetic lists the rule handle alone, which is the complete list.  Inventing a
  placeholder there would be worse than omitting it: `retract!` withdraws a conclusion by
  walking its justifications' antecedents, so a handle naming nothing retractable is a
  support that can never be taken away.  For a `prover-types/SupportingProver` it is *not*
  nothing, and omitting it would be the mirror mistake — a measure comparison holds
  because of a stored `conversionFactor` no other antecedent names, so a firing that
  omitted it would keep its conclusion after that row was retracted.

  `:matched` pairs each ordinarily matched fact with the **antecedent key it
  satisfied** (`rules/antecedent-key`, a functor or `[:not functor]`), which `:handles`
  alone cannot say: the join runs in cost order (`planned-join`), so a handle's position
  in the vector names nothing.  The pairing is what lets a firing tell which of its
  facts reached its antecedent through the `genl` hierarchy, and therefore which
  taxonomy edges it rests on (`subsumption-links`); the key rather than the bare functor
  because under a negation that climb runs the other way, and the bare functor is `not`
  for every negation there is.  A qualitative entailment's support handles are not
  paired: the network licensed them, not the taxonomy.

  `cpred` is the consequent predicate of the rule this join is running for, read by the
  transitive arm alone (`transitive-antecedent?`) and nil for a caller that has none."
  [kb ante states admit cpred]
  (cond
    ;; An `(unknown S)` antecedent is negation as failure, checked at *derive time* in
    ;; the conclusion's placement context — exactly where `exceptWhen` is checked, and
    ;; for the same reason: forward and backward must evaluate it in the same context.
    ;; It binds nothing and names no fact, so the join passes straight through; the
    ;; block decision is `naf-blocks?` in `place-conseq`, and later fact arrivals
    ;; re-block it through the same re-check path exceptions use.
    (sx/unknown? ante) states

    ;; An aggregate is evaluated per placement in `place-conseq` (docs/aggregate.md,
    ;; "Where the census is taken"), and `planned-join` withholds it.  A caller joining
    ;; an antecedent list directly reaches this arm, which passes it through rather than
    ;; letting the deferred arm below take the census in the wildcard context.
    (sx/aggregate? ante) states

    (deferred-antecedent? kb ante)
    (mapcat (fn [{:keys [bindings handles matched]}]
              (map (fn [[b sup]] {:bindings b :handles (into handles sup) :matched matched})
                   (solve-deferred kb ante bindings)))
            states)

    :else
    (let [ak    (rules/antecedent-key ante)
          calc  (qualitative-antecedent kb ante)
          keep? (when (and admit (nil? calc) (not (mirrored-antecedent? kb ante))) admit)
          perm? (permuting-antecedent? kb ante)
          hit   (mapcat (fn [{:keys [bindings handles matched]}]
                          (let [g (res/substitute ante bindings)]
                            (for [[h b2 stored] (join-matches kb g)
                                  :when (or (nil? keep?) (keep? h))
                                  ;; a fact read in another argument order holds the
                                  ;; firing only while a mark licensing that order does
                                  ms (if perm? (read-marks kb g b2 h stored) [[]])]
                              {:bindings (merge bindings b2) :handles (into (conj handles h) ms)
                               :matched  (conj matched [ak h])})))
                        states)]
      (cond
        calc (distinct (concat hit (solve-qualitative kb calc ante states)))
        (computed-antecedent? kb ante)
        (distinct (concat hit (solve-computed kb ante states)))
        (closure-antecedent? kb ante cpred)
        (distinct (concat hit (solve-closure kb ante states)))
        (transitive-antecedent? kb ante cpred)
        (distinct (concat hit (solve-computed kb ante states
                                              (transitive-contexts kb (nm/functor ante)))))
        (preserving-antecedent? kb ante '?ctx)
        (distinct (concat hit (solve-preserving kb ante states)))
        :else hit))))

(defn- open-ends
  "The two end variables of `ante` when it is a closure antecedent
  (`closure-antecedent?`) with both ends open, else nil.  `solve-closure` answers the
  pairs no edge states only once an end is bound, so `plan/order` holds the literal back
  until a generator binds one (`:end-vars`).  Canonical order stores `(genl ?a ?b)`
  ahead of `(pairOf ?a ?b)`, so without this an unranked join reads only the edges."
  [kb ante cpred]
  (when (and (sequential? ante) (= 3 (count ante)))
    (let [[_ a b] ante]
      (when (and (sx/variable? a) (sx/variable? b) (closure-antecedent? kb ante cpred))
        #{a b}))))

(defn- planned-join
  "Order `antecedents` by estimated fan-out under the bindings already in hand (`b0`),
  then join them left to right from `seed`.  Reordering a conjunction changes only how
  fast the answer is reached, never the answer set — and justification dedup is
  set-based (`jtms/has-justification?`), so the reordered `:handles` still dedup — so
  this is a pure cost decision, the same one `res/planned-antecedents` makes for the
  backward chainers.  `plan/order` pins the operational literals exactly as canonical
  antecedent order did: the deferred (evaluable) and `unknown` (NAF) literals never
  outrun what binds them, and the recursive literal stays put (`consequent-pred`).  A
  KB-registered evaluatable is not in that static set, so it is pinned by cost instead —
  the `:est-override` below reports it maximally unselective until its inputs are bound.
  Antecedents are substituted with `b0` before planning so the trigger's bindings make
  the estimates exact, mirroring the backward path.  A closure antecedent with both ends
  open waits for the literal that binds one (`open-ends`).

  The **post-join** literals are withheld entirely (`rules/post-join-literals`): an
  aggregate and everything reading its output are evaluated per placement context, so
  a join that ran them would either take the census in the wrong context or reach a
  comparison whose input nothing here can bind.  A **closed-extent** negative literal is
  withheld beside them (docs/naf.md): under the grant it is negation as failure, and a
  join over the stored negatives would answer a different question.

  `admit` is the arrival filter (`join-antecedent`), nil for a join that suppresses
  nothing.  It is per **handle** rather than per position, so the reordering above
  neither reads it nor disturbs it."
  [kb antecedents b0 consequent-pred seed admit]
  (let [subbed (mapv #(res/substitute % b0) antecedents)
        ;; ...and a closed-extent negative literal with them, for the sibling reason: it
        ;; is a **test** on what the conclusion's context believes, not a fact to look up,
        ;; so joining it would find only the stored negatives and miss the whole point of
        ;; the grant.  Decided in `derive-conclusion`, where `unknown` is decided.
        post   (into (set (rules/post-join-literals subbed))
                     (closed-extent-antecedents kb subbed))
        ;; A registered evaluatable is not in `plan/order`'s static deferred set, so it is
        ;; pinned after its binders by cost instead — computed, so maximally unselective
        ;; until its inputs are bound.  A literal a `SupportingProver` answers is costed by
        ;; that prover, since its stored rows are not its fan-out.  Every other antecedent
        ;; is ranked by the index model.
        ev     (provers/evaluatable-est-override (evaluatable-antecedent-preds kb))
        sp     (provers/support-est-override kb)
        est    (if ev (fn [g b] (or (ev g b) (sp g b))) sp)]
    (reduce (fn [states ante]
              (if (post ante) states (join-antecedent kb ante states admit consequent-pred)))
            seed
            (plan/order kb subbed '?ctx {:consequent-pred consequent-pred :est-override est
                                         :end-vars #(open-ends kb % consequent-pred)}))))

(defn- arrival-admit
  "The filter `complete-antecedents` puts on the handles the join yields, or nil when
  there is nothing to suppress — no ledger bound (outside a chaining run), a trigger the
  run never enqueued, or a trigger that is **not believed**.

  That last one is the asymmetry between the two ways a rule reaches a fact, and it
  is not optional.  A datum triggers on `res/match1`, which is a plain unify; the join
  finds facts through `*matcher*`, which is belief-filtered.  So an OUT datum — a
  defeated default — still fires its rules and still draws conclusions, while no
  *other* trigger's join can find it.  Its combinations are enumerable here and nowhere
  else, so here they are all made.  (A **superseded** spelling is the one OUT datum that
  never reaches a trigger at all, and `process-datum` says why.)

  **Admit a candidate whose arrival is at or before the trigger's**, which is semi-naive
  delta evaluation written for an agenda: every satisfying combination is enumerated by
  the trigger holding the *latest* arrival among its facts, and by no other, so a
  conclusion reached k ways costs k firings rather than k times the number of positions
  that could have started them.  A handle with no arrival is admitted — see
  `*agenda-arrivals*` for why that is the safe answer and not a gap.

  `<=` rather than `<` at every position, which admits one combination twice: the
  **self-join**, where one fact satisfies two positions of the same rule and so ties
  with itself.  Both of its triggers enumerate it, they build the identical
  justification, and the dedup rejects the second — a duplicate attempt for a shape a
  rule rarely has, against carrying each antecedent's original position through the
  cost planner's reordering to break the tie."
  [kb trigger-handle]
  (when-let [^java.util.Map arrivals *agenda-arrivals*]
    (when-let [at (.get arrivals trigger-handle)]
      (when (jtms/in? (reasoning/tms kb) trigger-handle)
        (let [at (long at)]
          (fn [h] (let [a (.get arrivals h)] (or (nil? a) (<= (long a) at)))))))))

(defn- rule-arrival-admit
  "`arrival-admit` for a **rule** datum's full join (`process-datum`): admit a fact that
  reached this run's agenda no later than the rule did, or never reached it.

  A firing's participants are its rule and its facts, and the one to enumerate it is the
  participant that arrived last.  A fact arriving after the rule enumerates the firing
  from its own trigger (`fire-rules-for`, where the rule is older and so not skipped),
  so the rule's join leaves that fact to it; a rule arriving after all its facts
  enumerates the firing here, and each of those facts skips the rule
  (`later-rule?`).  Without the rule in the comparison both sides enumerate every
  firing of a store seeded whole onto one agenda: `forward-chain` does exactly that,
  and a join pyramid placed each of its justifications twice.

  Nil — suppress nothing — outside a chaining run or for a rule the run never enqueued.
  The rule's belief was read by `process-datum` before it fired, so the believed-trigger
  condition `arrival-admit` puts on a fact is already met."
  [rule-handle]
  (when-let [^java.util.Map arrivals *agenda-arrivals*]
    (when-let [at (.get arrivals rule-handle)]
      (let [at (long at)]
        (fn [h] (let [a (.get arrivals h)] (or (nil? a) (<= (long a) at))))))))

(defn- complete-antecedents
  "Enumerate {:bindings :handles} completions of a rule fired at position
  `trigger-idx` by `trigger-handle`, joining the other antecedents from facts in
  any context, in cost order (`planned-join`).

  The other antecedents are joined only over facts that reached this run's agenda no
  later than the trigger did (`arrival-admit`), so a combination both sides could
  enumerate is enumerated by one of them.  The filter goes here, on the handles the
  join yields, rather than in the matcher: `*matcher*` is `rete`'s extension point and has to keep
  returning the identical set.

  **Any context on purpose** — the join passes `'?ctx` throughout.  Admissibility is
  placement's question: `place-conseq` requires a context that sees the rule and
  every antecedent fact (the common-descendant rule), and a firing it rejects is
  recorded as `:no-placement`.  Narrowing the join by some context's visibility
  would silently drop firings placement accepts, and turn a recorded outcome into
  a firing that never happened.

  A deferred literal at the trigger position is computed like any other, and the
  trigger handle is dropped.  That position is reachable — nothing stops a caller
  asserting `(lessThan 1 2)` as a fact, and the rule index keys the antecedent by its
  functor — but a computed literal must not draw support from a stored twin: the same
  firing arrives by every other antecedent's trigger with the literal *computed*, and
  two justifications for one conclusion that disagree about what supports it is the
  ambiguity the fix is meant to remove.  So a non-deferred trigger is recorded as a
  handle and dropped from the join; a deferred trigger is joined (computed) and the
  cost planner orders it among the rest.

  `marks` are the alternative sets of mark handles the trigger's own match rests on
  (`read-marks`), `[[]]` for a fact unified as it is stored; each seeds its own join, so a
  firing two marks license survives either one's retraction."
  [kb antecedents trigger-idx trigger-handle b0 marks consequent-pred]
  (let [trigger-ante (nth antecedents trigger-idx)
        handle-only? (not (deferred-antecedent? kb trigger-ante))
        to-join      (if handle-only?
                       (vec (keep-indexed (fn [j a] (when (not= j trigger-idx) a)) antecedents))
                       (vec antecedents))
        seed         (vec (for [ms (if handle-only? marks [[]])]
                            {:bindings b0
                             :handles  (if handle-only? (into [trigger-handle] ms) [])
                             ;; the trigger is a match like any other, and it is the one
                             ;; most likely to have subsumed: `fire-rules-for` reaches a
                             ;; rule through the arriving fact's *supertypes*
                             :matched  (if handle-only?
                                         [[(rules/antecedent-key trigger-ante) trigger-handle]]
                                         [])}))]
    ;; a *deferred* trigger draws no handle at all, so there is no arrival to order the
    ;; rest of the join against and nothing is suppressed
    (planned-join kb to-join b0 consequent-pred seed
                  (when handle-only? (arrival-admit kb trigger-handle)))))

(defn solve-rule
  "Full join of a rule's antecedents against current facts (used when a rule is
  added), in cost order.  The seeded arity starts from `b0` instead of the empty
  binding map, which is how `why-not` reconstructs a firing backwards from its
  conclusion; `consequent-pred` (the rule's consequent functor, nil if unknown) lets
  the planner keep the recursive literal in place."
  ([kb antecedents] (solve-rule kb antecedents {} nil))
  ([kb antecedents b0] (solve-rule kb antecedents b0 nil))
  ([kb antecedents b0 consequent-pred]
   ;; no trigger, so no arrival to order against: a full join suppresses nothing
   (planned-join kb (vec antecedents) b0 consequent-pred
                 [{:bindings b0 :handles [] :matched []}] nil)))

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

(defn- stamped-rule
  "The rule a generator stamped out, `sentence`, with the direction it is stored under.

  A stamped rule defaults to forward (forward + backward): a generator exists to
  materialize, and its stamped rule is the generator's product, so it forward-chains
  unless the author wrote a direction wrapper on it (which rides in the sentence and
  survives substitution).  Without this default a bare stamped rule would take the
  ordinary backward default and never fire — a generator that stamps nothing live."
  [sentence]
  (if (first (sx/peel-rule-wrapper sentence))
    sentence
    (rules/wrap-direction sentence :forward)))

(defn- stamped-rule-violation
  "The first check violation of the rules a stamped `sentence` is stored as in `pctx`,
  or nil — `mint-rule`'s check list, over every rule the polycanonicalization stores."
  [kb sentence pctx]
  (some #(checks/rule-violation kb % pctx) (rules/expand-rule (stamped-rule sentence))))

(defn- apply-removals!
  "Delete from the stores what a network removal swept — `integrate/fold-row!`'s tail."
  [kb {:keys [removed-sentexes removed-justifications] :as r}]
  (let [recs (:records kb)
        gone (into [] (keep #(p/get-sentex recs %)) removed-sentexes)]
    (doseq [sx gone] (integrate/sentex-removed! kb sx))
    (doseq [jid removed-justifications] (p/delete-justification! recs jid))
    (special/retire-unjustified-mints! kb r)))

(defn- mint-rule
  "Store the rule a **generator** firing stamped out (docs/generators.md), justified by
  the firing, and return its handle in the newly-created vector `place-conclusion`
  returns.

  One thing separates this from a rule somebody asserted, and it is the whole point of
  minting rather than macro-expanding: the mint is **derived**, so it is justified
  rather than marked a premise, and the ordinary relabel un-believes it the moment what
  licensed it goes.  Both chainers ask belief of a rule before using it
  (`res/rule-believed?`), so an un-believed mint stops firing without anything having to
  hunt it down and delete it.

  Everything else is what the assert entry point does, because a rule is a rule whichever entry point
  it came through: the same check list (`checks/rule-violation`, read through
  `checks/check-rule!` so the two cannot drift), the same rule postings
  (`special/index-rule-sentex`), and the direction the *stamped* rule's own
  `set/*Rule` wrapper set — which rides in the sentence and so survives substitution
  untouched.

  Returned as a new handle so the agenda takes it: a minted rule is a datum, and
  `process-datum` joins a forward-capable one over the facts already stored, exactly as
  it does for a rule somebody typed.  That is what makes a generator's two arrival
  orders agree — facts first or generator first, the same rules exist and have seen the
  same facts — without a retroactive sweep of its own.

  A refused mint is **dropped and recorded**, never thrown, for the reason every check
  on this path is a value: an exception escaping a firing would leave the fixpoint half
  computed, and which rule fired first would decide what the KB believes."
  [kb rule sentence pctx all-antes depth bindings strength subs]
  (let [sentence (stamped-rule sentence)
        ;; A stamped rule is polycanonicalized exactly as an asserted one is
        ;; (`rules/expand-rule`) — one rule per DNF alternative of a disjunctive
        ;; antecedent, and one per conjunct of a conjunctive consequent, each keyed by its
        ;; own predicates.  This is where a generator's stamped `or` expands: the holes are
        ;; ground by now, so the alternatives the mint stores are the alternatives of the
        ;; rule it stamped.  Checked before any of them is stored, for the reason
        ;; `core/assert` checks its conjuncts first: a mapv is not a transaction, and a mint
        ;; that half-landed would leave the KB holding part of a rule nobody wrote.
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
                 (when-not (jtms/has-justification? (reasoning/tms kb) (:name rule) all-antes h
                                                    (jtms/justification-key (:name rule) all-antes subs))
                   (let [jid  (p/next-id (:records kb))
                         ;; content order is bought here, inside the dedup guard, for
                         ;; `place-fact-conclusion`'s reason: the question above is
                         ;; set-keyed and only the record being written needs an order
                         just (jtms/->just jid (:name rule) (kb/antecedent-order kb all-antes)
                                           h bindings strength subs)]
                     (p/put-justification (:records kb) just)
                     (jtms/add-justification (reasoning/tms kb) just)))
                 (if new? [h] []))))
            minted))))

;; `place-conseq` declines to place a firing whose block condition already holds.  That
;; is the right call for the placement — the conclusion would be swept on the same
;; settle pass — but such a firing leaves **no trace**: no justification, no node,
;; nothing in `jtms/blocked`.  `settle` decides a pass is productive by asking whether
;; the blocked set moved, and reads a release off the justifications that were blocked
;; and are not any more, so both are blind to a firing that was never allowed to become
;; one, and the conclusion stays suppressed after the exception releases.  Belief then
;; depends on whether the block arrived before or after the facts, which is the
;; invariant docs/nmtms.md opens with.
;;
;; So the refusal is recorded, one level earlier and in the same shape: where the
;; blocked set holds justification ids, this holds `[rule-handle, bindings]` — enough to
;; re-ask the same level-6 question, and enough to place the conclusion from if the
;; answer moved.  Re-evaluating k recorded refusals costs k queries, in place of a join
;; over the whole fact extent.
;;
;; **Two of the four refusal reasons are recorded**, and the two that are not are not
;; oversights — and a fifth, which is not a refusal at all, rides the same record:
;;
;;   held exception    recorded — re-askable from the bindings alone
;;   `naf-blocks?`     recorded — likewise, and the same evaluator
;;   argument          recorded, as `:constraint` — a conclusion `place-fact-conclusion`
;;   constraint        dropped because an `arg` / `genlArg` / `interArg` / `quotedArg`
;;                     declaration convicts it.  That conviction reads the *absence* of a
;;                     path from the argument's types to the declared one, so it is
;;                     negation as failure over the taxonomy, and content arriving later
;;                     — a `genl` edge, a membership of the convicted term — can lift it.
;;                     Unrecorded, the firing was lost for good and belief depended on
;;                     whether the type arrived before the rule fired or after.  Re-asked
;;                     by `settle` when either can have moved (`constraint-refusals`).
;;   post-join failure not recorded — an aggregate is a *value* that moved, which is
;;                     `settle/rejoin-on-arrival-rules`' business: a queued aggregate
;;                     rule is re-joined whatever the blocked set did, so its firings
;;                     are found without a record
;;   `except`-hidden   not recorded — a visibility `except` moves what a context can
;;                     see rather than what the rule concludes, and no trigger queues
;;                     the rule on one; recording under a trigger that never fires
;;                     would be a set that grows and is never read
;;
;; A firing the settle blocks after its placement, and sweeps, is recorded the same way
;; (`record-swept-firing!`), so its release is the same narrow re-ask.
;;
;; The record is a **work list, never an answer**: it says which firings to re-ask, and
;; every entry is re-decided from scratch when it is read (`refusal-state`), exactly as
;; `exception-blocked-set` re-decides a candidate justification.  It is keyed on
;; content, so two refusals of the same rule at the same bindings from different passes
;; are one entry and arrival order cannot be read back out of it.  Nothing in it is a
;; nogood and nothing in it reaches `contradictions`: nothing was believed and nothing
;; conflicts, the rule simply did not fire.

(def max-refusals-per-rule
  "How many refused firings one rule's record keeps before it stops keeping them
  individually.

  One entry per refused firing is bounded by what a rule did **not** derive, and a rule
  excepted on a common condition can refuse far more than it places — so unlike blocking
  it is not bounded by the store.  Past this many entries the rule's record collapses to
  `:overflow` and it takes the coarse fallback instead: a queued overflowed rule forces a
  productive settle pass and is re-joined over its extent, which finds the same
  releases at the cost the record exists to avoid.  Correct on both sides of the line,
  and the line is stated in docs/exceptions.md."
  4096)

(defn- record-refusal!
  "Remember that a firing of `rule` was refused: the conclusion it would have placed,
  where, what it rests on, and the bindings the block condition was asked under.

  `:handles` are the antecedent *facts* alone, so the re-derivation recomputes the
  conclusion's depth exactly as a fresh firing would; `:antes` is the full justification
  antecedent list, rule handle and taxonomy supporters — `genl` and `genlCx` — included.

  `:max-depth` is the depth bound the **run that refused it** was configured with, kept
  so a later `release-refusal!` honours that bound rather than the default — the release
  runs in a settle with no run config in scope, so the bound has to travel with the
  entry.  `extra` rides into the entry as well: a `:constraint` drop's term and the
  taxonomy generations it was decided under (`record-constraint-drop!`), and a
  subsumed firing's `:subsumptions`.  It joins the entry's identity, so a firing refused under two different bounds is
  two entries; both release idempotently, and in practice a KB's runs share one bound."
  ([kb rule conseq pctx antes handles bindings max-depth]
   (record-refusal! kb rule conseq pctx antes handles bindings max-depth nil))
  ([kb rule conseq pctx antes handles bindings max-depth extra]
   (let [rh    (:rule-handle rule)
         entry (merge {:conseq conseq :pctx pctx :antes antes :handles handles
                       :bindings bindings :max-depth max-depth}
                      extra)]
     (swap! (reasoning/refused kb)
            (fn [m]
              (let [cur (get m rh)]
                (cond
                  (= :overflow cur)
                  m
                  (contains? cur entry)
                  m
                  (and cur (>= (count cur) max-refusals-per-rule))
                  (special/forget-kinds (assoc m rh :overflow) rh)
                  :else
                  (special/note-kind (assoc m rh (conj (or cur #{}) entry)) rh entry))))))))

(def ^:private constraint-drop-kinds
  "The violations a firing is dropped for that content arriving later can lift: each
  convicts one argument by the absence of a path from its types to a declared one, so
  a `genl` edge or a membership of that argument is what can change the answer."
  #{:arg-type :arg-genl :inter-arg-type :quoted-arg-type})

(def constraint-generations
  "The two closure generations an argument conviction is read through — `genl` for the
  argument's types, `genlCx` for which declarations and memberships its context sees.
  `special/taxonomy-generations` itself: `settle` compares this against the stamp
  `special` puts on a refused mint or lift, so the two cannot be two definitions."
  special/taxonomy-generations)

(defn- record-constraint-drop!
  "Record a firing `place-fact-conclusion` dropped on the argument conviction `v`, as a
  `:constraint` refusal: the convicted term (`checks/conviction-watch`) and the
  generations it was read under travel with it, so `settle` re-asks it only when one of
  them can have moved.  `:handles` is the whole antecedent list, which is what the
  release recomputes the depth from; the rule handle and the taxonomy supporters in it
  sit at depth 0."
  [kb rule conseq pctx all-antes bindings subs v]
  (let [antes (kb/antecedent-order kb all-antes)]
    (record-refusal! kb rule conseq pctx antes antes bindings nil
                     (cond-> (merge {:constraint true :gens (constraint-generations kb)}
                                    (checks/conviction-watch v))
                       subs (assoc :subsumptions subs)))))

(defn record-swept-firing!
  "Record the rule firing whose justification record is `j` as a refusal, when the
  settle blocks it after its placement and the sweep deletes it: the entry a firing
  refused at its placement would have recorded, so the trigger that lifts the block
  releases it from its bindings (`release-refusal!`) and not by a join over the rule's
  extent.  `:handles` is every antecedent but the rule.  Records nothing for a firing
  an `except` hides an antecedent of at its placement, which the refusal record does not
  hold (docs/exceptions.md, \"A refused firing is remembered as bindings\").  Reads the
  conclusion's record, so it runs before the sweep's records are deleted."
  [kb j]
  (let [rh (:informant j)]
    (when (integer? rh)
      (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
        (let [antes (vec (:antecedents j))
              pctx  (:context csx)]
          (when-not (antecedent-hidden? kb antes pctx)
            (record-refusal! kb {:rule-handle rh} (:sentence csx) pctx antes
                             (into [] (remove #{rh}) antes) (:bindings j) nil
                             (when-let [subs (:subsumptions j)] {:subsumptions subs}))))))))

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
  "Drop the fact conclusion `conseq` for violation `v`: report it, and remember an
  argument conviction for `settle` to re-ask once a type arriving later can lift it.
  Returns the empty vector of new handles a placement that stored nothing returns."
  [kb rule conseq pctx all-antes bindings subs v]
  (violations/report kb [(assoc v :sentence conseq :context pctx :rule (:rule-handle rule))])
  (when (constraint-drop-kinds (:violation v))
    (record-constraint-drop! kb rule conseq pctx all-antes bindings subs v))
  [])

(defn- visibility-support
  "A witness for each context `pctx` had to see to hold the firing: the `genlCx` edge
  handles along one path per ingredient context (`tax/reach-support`), deduplicated
  where two ingredients share a stretch of the ancestor set.

  The `genl` half above and this one are the same claim about two relations.  A
  placement is the maximal context that **sees** the rule, the facts and the edges the
  match climbed, and every one of those sightings is a `genlCx` reachability some
  ordinary sentex supports and somebody can take back.  Naming the sighted contexts and
  not the edges that reach them would leave the conclusion standing in a context that
  can no longer see its own reasons, and the same KB built without the edge derives
  nothing — belief as a function of arrival order, which is the invariant
  docs/nmtms.md opens with.

  **The ordinary firing pays one `=` per ingredient and reads no closure**: a rule and
  its facts in the placement's own context reach it reflexively, and a reflexive reach
  rests on nothing.  A supporter with no recorded context is seen from everywhere and
  is skipped for the same reason.

  One path, one supporter per edge, exactly as `subsumption-support` names one: a
  justification is a conjunction of supports rather than a proof that no other support
  exists, so a second route re-derives at a fresh handle when the named one goes
  (`special/resubsumption-seeds` does the same office for `genl`)."
  [tax pctx ctxs]
  (if (every? #(or (nil? %) (= pctx %)) ctxs)
    []
    (into []
          (comp (remove #(or (nil? %) (= pctx %)))
                (distinct)
                ;; asked from the placement's own view, so a path it reads as hidden or
                ;; withdrawn is never the one named when another reaches
                (mapcat #(tax/reach-support tax :genlCx pctx % pctx))
                (map first)
                (distinct))
          ctxs)))

;; ---- a nogood places its conclusions -------------------------------------

(def nogood-informant
  "The informant of every justification a placed nogood stores (`place-nogood!`)."
  exc/nogood-informant)

(defn- context-edge?
  "Is the sentex at `h` a `genlCx` edge?"
  [kb h]
  (= 'genlCx (nm/functor (:sentence (p/get-sentex (:records kb) h)))))

(defn- placement-justifications
  "The justifications under `nogood-informant` of the placed sentexes `hs` that `keep?`
  holds of, each with its `:core`: its antecedents but the `genlCx` edges, the members and
  grounds of the nogood it places."
  [kb hs keep?]
  (let [tms (reasoning/tms kb)]
    (into []
          (comp (mapcat #(jtms/supports tms %))
                (distinct)
                (keep #(jtms/justification tms %))
                (filter #(and (= nogood-informant (:informant %)) (keep? %)))
                (map (fn [j] (assoc j :core (into #{} (remove #(context-edge? kb %))
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
  unless given) at `:default`, and return its handle when the record is new."
  ([kb sentence pctx antes] (justify-placed! kb sentence pctx antes nogood-informant))
  ([kb sentence pctx antes informant]
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
       (let [just (jtms/->just (p/next-id recs) informant antes h {} :default)]
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
    (if (< (count within) (count (reads/as-stored-with-term (:index kb) (sx/sentex-handle h))))
      (let [[ctr] (placed-sentences kb members nil)
            ss    (into [ctr] (map #(list sx/defeat-functor (sx/sentex-handle %))) members)]
        (keyed-placements
         (into [] (for [ctx within, s ss
                        :let [ph (kb/find-sentex-handle kb s ctx)]
                        :when ph
                        j (placement-justifications kb [ph] any?)]
                    (assoc j :key [s ctx (set (:antecedents j))])))))
      (filterv #(contains? within (second (:key %))) (placed-justifications kb h)))))

(defn- membership-owned?
  "Is the placed nogood over `members` with antecedents but the `genlCx` edges `core` one
  the membership families place (`place-memberships!`): a ground among `core` supports a
  separation or cover declaration (`tax/separation-ends`)?"
  [kb members core]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (some (fn [h] (some #(tax/separation-ends tax %) (tax/supported-keys tax [h])))
                   (remove (set members) core)))))

(defn- place-justified!
  "Place the nogood over the handles `members` at each `[context antecedents]` of
  `placements`: `(contradicts …)` naming the members in content order, and, when
  `decide/verdict` over the members' classes in the network names a unique weakest member
  `L`, `(defeat (sentexHandle L))`, each justified under `nogood-informant` at `:default`
  by the antecedents.  Every justification an earlier placement of the same members
  stored under a core `owns?` takes that `placements` no longer gives is dropped, and the
  sweep collects a placed sentex it leaves unsupported.  Returns the handles it created.
  With `placements` empty this removes the nogood's placements `owns?` takes.  With the
  context set `within`, only the placements in it are compared, and the caller passes
  only the `placements` in it (`placed-justifications-within`)."
  ([kb members placements owns?] (place-justified! kb members placements owns? nil))
  ([kb members placements owns? within]
   (let [tms     (reasoning/tms kb)
         tax     (reasoning/taxonomy kb)
         recs    (:records kb)
         members (set members)
         verdict (decide/verdict #(or (jtms/defeat-class tms %) :default)
                                 #(boolean (some->> (p/get-sentex recs %) :sentence
                                                    (decide/roster-literal? tax)))
                                 members)
         ss      (when (seq placements) (placed-sentences kb members verdict))
         want    (into #{} (for [[pctx antes] placements, s ss] [s pctx (set antes)]))
         have    (into {} (comp (filter #(and (= members (:members %)) (owns? (:core %))))
                                (map (juxt :jid :key)))
                       (if within
                         (placed-justifications-within kb members within)
                         (placed-justifications kb (first members) members)))
         gone    (into [] (keep (fn [[jid k]] (when-not (contains? want k) jid))) have)
         added   (nm/sort-by-content-key (fn [[s pctx]] [s pctx]) (remove (set (vals have)) want))
         _       (when (seq gone)
                   (apply-removals! kb (reduce (fn [acc jid]
                                                 (let [r (jtms/drop-justification! tms jid)]
                                                   (p/delete-justification! recs jid)
                                                   (merge-with into acc r)))
                                               nil gone)))
         made    (mapv (fn [[s pctx antes]] [s (justify-placed! kb s pctx antes)]) added)]
     (into [] (keep second) made))))

(defn place-nogood!
  "Place the nogood over the handles `members`, detected with the handles `grounds`, at
  each maximal context that sees the contexts the members and grounds are stated in and
  where no except hides one of them (`res/exception-aware-placements`, the placement a
  firing's conclusion takes), each justified by the members, the grounds and the `genlCx`
  edges the placement sees them over (`visibility-support`), so retracting any of them
  takes it OUT (`place-justified!`, over the placements of the same members and grounds).
  Returns the handles it created.  The caller states the nogood: every member IN in the
  network.  With the context set `within`, only the placements in it are compared
  (`place-justified!`): a `genlCx` move changes the placements in the contexts whose
  ancestor sets it changed and no others (`decide/edge-reach`'s `:under`).  See
  docs/nmtms.md."
  ([kb members grounds] (place-nogood! kb members grounds nil))
  ([kb members grounds within]
   (let [tax  (reasoning/taxonomy kb)
         recs (:records kb)
         core (into (set members) grounds)
         ctxs (into [] (comp (map #(:context (p/get-sentex recs %))) (distinct)) core)]
     (place-justified! kb members
                       (for [pctx (cond->> (res/exception-aware-placements kb core ctxs)
                                    within (filter within))]
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
  (`negation/take-moved!`), of the bodies with a member among the handles `fresh` the
  pass relabelled (a stored member among them) or `placed` (`placed-members`), and of the
  bodies with a member stated in a context of `reach`'s `:below` (`decide/edge-reach`,
  `reads/as-stored-opposed-in`).  A pair reached through `:below` alone compares only its
  placements in `reach`'s `:under`.  Every body stored in both polarities when `first?`
  (`decide/take-edge-cursor!`) or the relation was rebuilt.  A pair is placed when both
  members are IN in the network (`jtms/network-in?`); a pair with a member OUT keeps its placements OUT through their
  justifications.  Reads one count while no body is stored in both polarities."
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
      (into []
            (comp (filter (fn [[[n q]]] (and (jtms/network-in? tms n) (jtms/network-in? tms q))))
                  (mapcat (fn [[[n q] within]] (place-nogood! kb #{n q} #{} within))))
            (nm/sort-by-content-key
             (fn [[pair]] (into [] (mapcat #(let [s (p/get-sentex (:records kb) %)]
                                              [(:sentence s) (:context s)]))
                                pair))
             (concat (map vector (negation/pairs kb full))
                     (when under
                       (map #(vector % under) (negation/pairs kb reached)))))))))

;; ---- a placement climbs the genl edges a match subsumed through --------

(defn- subsumption-links
  "The `[sub super]` predicate pairs a firing reached through **predicate/type
  subsumption** — one per matched fact that did not satisfy its antecedent on the
  antecedent's own key.

  Both sides are read as `rules/antecedent-key`s, a functor or `[:not functor]`, which
  is what carries the **polarity** the direction depends on.  A positive fact satisfies
  a positive antecedent by being on a *spec* of it, so the fact is the sub; a negated
  fact satisfies a negated antecedent by being on a *genl* of it — subsumption runs the
  other way under a negation (`res/match1`) — so there the *antecedent's* body is the
  sub.  A key of one polarity against a key of the other never subsumed: the match was
  a plain unify, and polarity does not cross.

  A `genl` antecedent answered from the closure (`solve-closure`) records its pair on
  `:matched` as `[key nil [sub super]]`, with no fact behind it, and the pair is the link.

  Empty for every ordinary firing, which is what keeps this free: a fact matches an
  antecedent of its own key, so one `not=` pass answers it before any pipeline is built
  or closure read.  `record-of` is the firing's already-fetched records; a matched handle
  with no record (swept mid-run) is skipped rather than guessed at.

  Read **upward from the sub**, not downward from the super: `sub ∈ specs(super)` and
  `super ∈ genls(sub)` are the same reachability on the same edges, and the up-closure
  of a term is its chain to `thing` where the down-closure of a general antecedent can
  be most of the hierarchy (OpenCyc's `thing` has six figures of them).  Same answer,
  and the memo it fills is the small one.

  The global closure is the gate, not a placement's: whether the two predicates are
  related at all is a property of the KB, and *which* contexts can see the relating
  edges is `subsumption-support`'s question, asked once per placement."
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
                  (filter (fn [[sub super]] (contains? (tax/genls-global tax sub) super))))
            matched))))

(defn- subsumption-support
  "A witness for each of a firing's subsumptions, as `[handle ctx]` supporter pairs
  (`tax/reach-support`) — or nil when `vantage` sees no path for one of them.  A nil
  `vantage` asks globally, which is what placement does: the edges are an *ingredient*
  of the firing, so their contexts are an input to deciding where it lands rather than
  a test on a decision already made.

  A fact that satisfied an antecedent it does not key with did so over a `genl` path,
  and a conclusion that rests on that path may only live where the path is visible —
  otherwise a context believes `(ancestorOf Tom Bob)` on the strength of a
  `(genl fatherOf parentOf)` edge some sibling theory asserted and it cannot see.
  Feeding the supporters' contexts to `maximal-common-descendant-contexts` beside the
  rule's and the facts' makes that structural: every placement it returns sees every
  edge by construction, so there is nothing left to filter, and the firing's three
  ingredients — rule, facts, taxonomy — are treated alike.

  The join itself stays global (`complete-antecedents`, any context on purpose): which
  facts *exist* is not the placement's question, and narrowing the join would drop
  firings placement accepts."
  [kb links vantage]
  ;; the widest-bottleneck route: a firing that climbed the genl closure
  ;; rests on the *strongest* path relating the two functors, not the shortest, so its
  ;; conclusion is capped at that path's floor.  `supporter-class` is the live JTMS
  ;; defeat-class of each edge supporter, read here where the tms is in hand.
  (let [supporter-class #(jtms/defeat-class (reasoning/tms kb) %)]
    (reduce (fn [acc [sub super]]
              (if-let [hs (tax/reach-support (reasoning/taxonomy kb) :genl sub super
                                             vantage supporter-class)]
                (into acc hs)
                (reduced nil)))
            []
            links)))

(defn- descent-placements
  "`{placement [edge-handle …]}` for a subsumed firing whose conclusion descends below the
  contexts that see the rule and the facts: one entry per maximal context that sees the
  ingredients and every edge of one witness combination.

  A combination is one route per subsumption, and every combination no other covers is
  placed (`tax/reach-supports`, `tax/uncovered`): a route covers another when its floor
  class is at least as strong and every reader that sees the other also sees it.  Two
  routes stated in contexts neither of which sees the other each place the conclusion
  below their own context, so each reader that reaches over its own edges reads it, and
  no placement depends on which route arrived first.  A placement two combinations
  decide names the first in content order.  nil when some subsumption has no route the
  view sees."
  [kb links ingredients]
  (let [tax      (reasoning/taxonomy kb)
        tms      (reasoning/tms kb)
        rank     #(strength/rank-of (or (jtms/defeat-class tms %) :default))
        per-link (mapv (fn [[sub super]]
                         (tax/reach-supports tax :genl sub super nil
                                             #(jtms/defeat-class tms %)))
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
                             (tax/maximal-common-descendant-contexts tax ectxs)))))
                {} combos)))))

(defn- placements-over*
  "`placements-over` under the network reading it binds."
  [kb links supporters ingredients]
  (let [tax  (reasoning/taxonomy kb)
        base (res/exception-aware-placements kb supporters ingredients)]
    (if (empty? links)
      ;; no subsumption to witness, so the whole support map is the visibility one —
      ;; and it is empty for the firing whose rule and facts are where the conclusion
      ;; lands, which is nearly all of them
      [base (reduce (fn [m b]
                      (let [vs (visibility-support tax b ingredients)]
                        (if (seq vs) (assoc m b vs) m)))
                    {} base)]
      (let [seeing (reduce (fn [m b]
                             (if-let [hs (subsumption-support kb links b)]
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
                              (descent-placements kb links ingredients))]
            (when (or (seq seeing) (seq descent))
              [(into (filterv seeing base)
                     (nm/sort-by-content-key nm/print-key compare (keys descent)))
               (merge descent seeing)])))))))

(defn- placements-over
  "`placement-ingredients`' answer for the `genl` subsumptions `links`, the supporter
  handles `supporters` and their contexts `ingredients`: `[placement-contexts
  {placement-context [edge-handle]}]`, or nil when no context places them.  The
  candidates are the maximal contexts that see every supporter where no except hides one
  (`res/exception-aware-placements`).  A placed nogood reads it with its members and grounds
  as the supporters (`route-placements`), and a guard defeat with its blocker handles
  (`guard-defeat-placements`), so a premise except sweeps its placement as it sweeps a
  firing's, and a member its own `defeat` hides is no reason to move it.  Every
  witness search here reads the network and the `except` roster, and no placed `defeat`
  (`tax/*network-belief*`), so a defeat of a `genl` supporter moves no placement."
  [kb links supporters ingredients]
  (binding [tax/*network-belief* true]
    (placements-over* kb links supporters ingredients)))

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

(defn- guard-solutions
  "The solutions of the block condition `conds` under `bindings`, as the join's
  `{:bindings :handles :matched}` states: the forward join over its conjuncts
  (`solve-rule`), a `thereExists` contributing its body.  A conjunct a prover answers from
  stored facts (a transitive walk, a `SupportingProver`, the `genl` closure) names the
  facts it read, as a firing's antecedent does.  An `unknown` binds nothing and passes
  through, so the condition holds or fails at the placed context
  (`guard-defeat-placements`), never by what an unseen context stores.  `cpred` is the
  rule's consequent functor."
  [kb conds bindings cpred]
  (let [flat (fn flat [cs] (mapcat #(if (sx/there-exists? %) (flat (sx/conjuncts (nth % 2))) [%]) cs))]
    (solve-rule kb (mapv #(sx/canon (res/substitute % bindings)) (flat conds)) bindings cpred)))

(defn- guard-conditions-of
  "`block-conditions` read off the chainer's rule view (`rule-view-of`)."
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

(defn- guard-defeat-placements
  "`#{[context antecedents]}`: where the firing `j`, a justification record of a rule,
  owes a guard defeat of its conclusion F.  For each solution of a block condition read
  with no context (`guard-solutions`), each context `placements-over` gives for the
  handles the solution read, over their contexts and F's, with the `genl` pairs its match
  climbed (`subsumption-links`), other than F's own context, where the condition holds
  in the network and through the excepts (`provers/exception-holds?` under
  `tax/*network-belief*`), so a blocker a defeat hides there still places one.  Each
  except or defeat that can take a blocker's defeat out of force
  (`blocker-support-hiders`) is one more supporter, placed the same way; a context that
  sees a placement the solution gives without it takes none (design ruling 23).  The antecedents are those handles, the
  `exceptWhen`'s own handle, the firing's rule and antecedents, F, and the `genl` and
  `genlCx` edges `placements-over` names for the context.  `given` is `block-conditions`'
  answer, when the caller holds it."
  [kb j given]
  (let [recs (:records kb)
        rh   (:informant j)
        f    (:consequence j)
        rsx  (when (integer? rh) (p/get-sentex recs rh))
        pctx (:context (p/get-sentex recs f))]
    (if-not (and pctx rsx (rules/rule? rsx))
      #{}
      (let [b      (settled-bindings kb (:bindings j) pctx)
            core   (-> (set (:antecedents j)) (conj rh f))
            rec    #(p/get-sentex recs %)
            tax    (reasoning/taxonomy kb)
            holds? (fn [conds q] (and (not= q pctx)
                                      (binding [tax/*network-belief* true]
                                        (provers/exception-holds? kb conds b q))))
            placed (fn [conds links blk]
                     (let [ctxs   (into [pctx] (comp (keep #(:context (rec %))) (distinct)) blk)
                           [ps m] (placements-over kb links blk ctxs)]
                       (into [] (comp (filter #(holds? conds %))
                                      (map (fn [q] [q (-> core (into blk) (into (get m q)))])))
                             ps)))]
        (into #{}
              (for [[conds hs] (or given (block-conditions kb rh rsx))
                    {sup :handles matched :matched}
                    (distinct (map #(select-keys % [:handles :matched])
                                   (guard-solutions kb conds b (nm/functor (:consequent rsx)))))
                    :let [blk   (into hs sup)
                          links (subsumption-links kb matched rec)
                          base  (placed conds links blk)
                          bctxs (mapv first base)]
                    pl (into base
                             (comp (mapcat #(placed conds links (conj blk %)))
                                   (remove (fn [[q]] (some #(tax/sees? tax q %) bctxs))))
                             (blocker-support-hiders kb blk f))]
                pl))))))

(defn- guard-justifications
  "`{jid [sentence context antecedents]}`: the justifications under `guard-informant`
  that the firing `j` owns, those resting on its conclusion whose antecedents hold its
  rule and every antecedent of it."
  [kb j]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        core (conj (set (:antecedents j)) (:informant j))]
    (into {}
          (comp (keep #(jtms/justification tms %))
                (filter #(= guard-informant (:informant %)))
                (keep (fn [g] (let [as (set (:antecedents g))]
                                (when (every? as core)
                                  (let [c (p/get-sentex recs (:consequence g))]
                                    [(:id g) [(:sentence c) (:context c) as]]))))))
          (jtms/dependents tms (:consequence j)))))

(defn place-guard-defeats!
  "For each `[j live? conds]` of `firings`, `j` a firing's justification record and
  `conds` its block conditions or nil (`guard-defeat-placements`): store
  `(defeat (sentexHandle F))`, F its conclusion, at each context `guard-defeat-placements`
  names, justified there under `guard-informant` at `:default`, and drop each guard
  justification the firing owns (`guard-justifications`) that the current state no longer
  gives.  A firing that is not `live?`, blocked or gone, keeps none.  A change posts F's
  re-check (`special/recheck-defeat-target`).  Returns the conclusions whose guard
  defeats moved.  The defeat is read at read time (`exc/defeat-hidden-fn`, its coverage);
  `chain` reads none.  See docs/naf.md."
  [kb firings]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        place!
        (fn [[j live? conds]]
          (when (p/get-sentex recs (:consequence j))
            (let [s     (list sx/defeat-functor (sx/sentex-handle (:consequence j)))
                  want  (into #{} (map (fn [[q antes]] [s q antes]))
                              (when live? (guard-defeat-placements kb j conds)))
                  have  (guard-justifications kb j)
                  gone  (into [] (keep (fn [[jid k]] (when-not (contains? want k) jid))) have)
                  added (nm/sort-by-content-key (fn [[s q]] [s q]) (remove (set (vals have)) want))]
              (when (seq gone)
                (apply-removals! kb (reduce (fn [acc jid]
                                              (let [r (jtms/drop-justification! tms jid)]
                                                (p/delete-justification! recs jid)
                                                (merge-with into acc r)))
                                            nil gone)))
              (doseq [[s q antes] added] (justify-placed! kb s q antes guard-informant))
              (when (or (seq gone) (seq added))
                (special/recheck-defeat-target kb {:sentence s})
                (:consequence j)))))]
    (into [] (keep place!) firings)))

;; ---- a firing places its conclusion -------------------------------------

(defn- place-fact-conclusion
  "Persist/justify a rule conclusion `conseq` in context `pctx` at justification
  `strength` (:monotonic / :default); return the handles newly created (for
  enqueueing) — the conclusion itself, plus a copy in each context its predicate is
  declared to lift into.

  The definitional constraints — arg types, disjointness, functionality — hold of
  *derived* content as much as of asserted content, and they are checked here, on the
  derivation path, through `checks/constraint-admission`.  So is stratification, for
  the one conclusion that can break it: a derived `genl` / `genlCx` edge that would
  close a cycle through negation.

  A clash with a second believed sentex — disjointness, functionality, asymmetry — is
  **placed**, not dropped.  A rule that concludes `(cat Rex)` where `(dog Rex)` is
  believed and the two are declared disjoint stores the conclusion, and `settle` weighs
  the pair: the stronger defeat class wins, and an equal `:default` pair stays believed
  and is reported by `core/contradictions`.  `assert` refuses the same pair, because a
  caller is there to be told; a firing has no caller.

  A violation with no second side is **dropped and recorded**, never thrown: a malformed
  sentence, a name the naming policy refuses, an argument constraint, or a
  stratification cycle.  Chaining is a fixpoint
  and must not abort halfway through it, and an exception escaping a rule firing would
  make the resulting belief set depend on which rule happened to fire first.  The
  conclusion is skipped (no sentex, no justification) and the violation lands in the
  KB's `violations` atom, readable with `core/violations`.  An argument-constraint drop
  is remembered as well (`record-constraint-drop!`), for `settle` to place once a type
  arriving later lifts the conviction.

  Dropping an argument-constraint violation rather than arbitrating it is deliberate, and
  docs/nmtms.md holds the reason: an argument constraint convicts by the **absence** of a
  path from the argument's types to the constraint type, so there is no second sentex to
  weigh the conclusion against and nothing for a defeat class to compare.  A nogood needs
  two sides; this has one."
  [kb rule conseq pctx all-antes depth bindings strength subs]
  (let [existing (kb/find-sentex-handle kb conseq pctx)
        ;; Checked only when the conclusion is **new**.  Re-deriving a sentence already
        ;; stored in this context adds a *justification*, not content — whatever it says
        ;; was admissible when it was first placed, so a second derivation of it cannot
        ;; introduce a violation that was not already there.  This is not a
        ;; micro-optimization: `args-problem` runs `isa?`, which walks a type's whole spec
        ;; closure with an index lookup per subtype, and forward chaining re-derives the
        ;; same conclusion on every round of every defaults pass.  Paying it per firing
        ;; rather than per new conclusion made the starter's load ten times slower.
        ;; ...and the rule-set constraint alongside them: a derived `genl` edge
        ;; reaches the taxonomy through `integrate-transitive` below, so it can close
        ;; a cycle through negation with no caller asserting anything.  Same
        ;; treatment — dropped and reported, never thrown.
        ;; one pass over the definitional checks, answering both halves: the violation
        ;; that drops the conclusion, and — for an admitted one — what the argument
        ;; constraints entail about its arguments, materialized below once it has a
        ;; handle to be justified against
        adm      (when-not existing (checks/constraint-admission kb conseq pctx))
        v        (when-not existing (fact-violation kb rule conseq pctx adm))
        ;; ...and the roster check, which a stored conclusion owes as well: a firing it
        ;; convicts is stored, held void and reported, so it supports nothing while the
        ;; roster rules it out and supports its conclusion once the roster stops
        forced   (when-not v (checks/forced-conclusion-violation kb (:rule-handle rule) conseq))]
    (if v
      (drop-fact-conclusion! kb rule conseq pctx all-antes bindings subs v)
      (let [[h s new?] (if existing
                         [existing (p/get-sentex (:records kb) existing) false]
                         (let [[h s] (kb/create-sentex kb conseq pctx)] [h s true]))
            ;; the dedup key, built once for the question and the add that follows it
            jkey       (jtms/justification-key (:name rule) all-antes subs)]
        (when forced
          (violations/report kb [(assoc forced :sentence conseq :context pctx
                                        :rule (:rule-handle rule))]))
        ;; a new conclusion takes its forced memberships before anything can label it
        (when new? (checks/force-sentex! kb s))
        ;; the derivation-path choke point: a derived genl edge reaches the closure,
        ;; and a derived fact is a re-check trigger like an asserted one
        (when new? (special/derived-sentex-added kb s h))
        (jtms/ensure-node (reasoning/tms kb) h depth)
        (when-not (jtms/has-justification? (reasoning/tms kb) (:name rule) all-antes h jkey)
          (let [jid  (p/next-id (:records kb))
                ;; **The content sort is paid here and nowhere earlier.**  `all-antes`
                ;; arrives in the order the join built it; the record about to be
                ;; written is the one thing that must not inherit it
                ;; (`kb/antecedent-order` says what reads it).  The dedup question just
                ;; above is keyed on the antecedents **as a set** (`jtms/just-key`), so
                ;; it answers the same either way — and ordering before the guard priced
                ;; a printed sentence per antecedent per *firing* where the record being
                ;; written is per *justification*.
                ;; The rule's own handle is sorted out rather than in: `->just` drops
                ;; the informant from the stored vector, dropping one element of a
                ;; sorted vector leaves the rest in order, and keying the rule would
                ;; rebuild its whole `implies` sentence to compare it.
                inf  (:name rule)
                just (jtms/->just jid inf (kb/antecedent-order kb (remove #(= inf %) all-antes))
                                  h bindings strength subs)]
            (when forced (jtms/set-forced (reasoning/tms kb) :void [jid] true))
            (p/put-justification (:records kb) just)
            (jtms/add-justification (reasoning/tms kb) just jkey)
            ;; a guard that holds below the placement places a defeat of the firing
            (when (and (integer? inf) (:watched? rule))
              (place-guard-defeats! kb [[just true (guard-conditions-of rule)]]))
            ;; a firing over a route the witness rule now names replaces the same firing
            ;; over the route it named before, which only a stored conclusion can hold
            (when-not new?
              (apply-removals! kb (special/drop-replaced-routes! kb just)))
            ;; a conclusion a permuting mark re-spelled keeps the spelling it was drawn
            ;; in, for the mark's leaving to put it back at (`reconcile-spellings!`)
            (when (and (not= conseq (:sentence s)) (integer? (:name rule))
                       (integrate/permuting? kb (res/permuted-functor conseq)))
              (integrate/note-derived-spelling! kb h jid conseq))))
        ;; Everything a conclusion means beyond itself, in the order `assert-entry/assert-one`
        ;; runs the same list — the three ways it merges, the copy a decontextualized
        ;; predicate takes, and what the argument constraints entail — because each is a
        ;; claim about the predicate rather than about how the sentence arrived.
        (let [;; A rule concluding one of the three equality relations merges exactly as
              ;; an asserted one does: the closure learns the edge, migration restates
              ;; every sentex the edge displaces, and the twins are new content this run
              ;; has to see.  Without it the conclusion would be stored and believed while
              ;; the closure never learned it — and `recover`, which replays the store,
              ;; would then disagree with the running KB about what it entails.  Reached by
              ;; name rather than by the `:derived?` flag `genl` carries, because
              ;; `integrate-transitive` discards what an arm returns and here the return
              ;; value is the work: the twins and the violations.  **After the
              ;; justification above**, not beside `derived-sentex-added`: migration
              ;; justifies each twin by the equality edges it rests on and takes only the
              ;; ones it believes, so a line earlier the conclusion is a node nothing
              ;; supports and the merge writes nothing.
              eq   (when (and new? (kb/equality-sentence? conseq))
                     (special/integrate-equality-sentex kb s h))
              ;; A *derived* second value for a functional predicate merges exactly as an
              ;; asserted one does.  It has to be here as well as in `assert-one`, because
              ;; `functional-problem` does not refuse a symbol clash (it derives an
              ;; equality instead): without this a rule concluding `(motherOf Tom
              ;; MrsSmith)` alongside `(motherOf Tom Mary)` would leave two values of a
              ;; functional predicate believed and unreconciled.
              fnl  (when new? (special/derive-functional-equalities kb conseq pctx h))
              ;; ...and the declaration's own side of the same inference: a rule
              ;; concluding `(functional P)` reaches P's stored facts exactly as an
              ;; asserted one does, or which values a slot reconciles would depend on
              ;; whether the declaration was written or derived.  A declaration the
              ;; labeller holds OUT, such as one a void firing concludes, derives no
              ;; equality here: the settle that brings it IN runs the same sweep
              ;; (`special/revived-declaration-sweeps`), so the equality arrives with the
              ;; mark's belief and migrates then
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
              ;; ...and a derived `genlCx` edge restates the sentexes its widened ancestor set
              ;; newly exposes to a merge, as an asserted one does — or which spelling a
              ;; context reads a fact under would depend on whether the spindle was
              ;; written or inferred
              ;; ...and the fourth arrival order of the functional/antisymmetric merge, a
              ;; derived `genlCx` edge making two already-marked facts jointly visible for
              ;; the first time, exactly as an asserted one does.  **A rule-concluded edge
              ;; is placed here and never through the assert entry point**, so this line is the
              ;; whole of what runs the equality reconcilers for it — which is why it is
              ;; the same call `assert-one` and the structural producer make rather than a
              ;; third hand-written copy of the list (vaelii#56).  And it sits *after* the
              ;; justification above for that call's own reason: the sweeps read the
              ;; belief-filtered genlCx closure, and a line earlier the conclusion supports
              ;; nothing and the ancestor set has not widened
              cxe  (when new? (special/reconcile-context-edge kb conseq))
              ;; ...and a *derived* `(symmetric P)` re-spells the rows stored before it
              ;; exactly as an asserted one does — the mark sorts arguments at the entry point,
              ;; so without this whether one proposition is one record would depend on
              ;; whether the declaration was written or inferred
              symx (when new? (integrate/commute-existing kb conseq h))
              ;; nil when nothing merged, which is every conclusion on a KB that states
              ;; no equality and every re-derivation on one that does — and a fixpoint
              ;; re-derives the same conclusion on every round of every defaults pass, so
              ;; this is the arm that must added no work rather than a little
              mig  (when (or eq fnl fex fed asym axe axd cxe symx)
                     (merge-with into {:new [] :superseded [] :violations []}
                                 eq fnl fex fed asym axe axd cxe symx))
              ;; The spellings those merges retired, applied here rather than left to the
              ;; settle that follows.  A supersession *starts* when migration says so and
              ;; reaches the reconcile only as its `extra` (`special/supersession-map`),
              ;; so a merge whose entries nobody hands over displaces nothing at all and
              ;; the KB believes both spellings until something restarts it.  It is the
              ;; same call `assert` makes before it chains, and it is what makes the twins
              ;; below seeds rather than an optimization: the retired spelling stops
              ;; matching the moment this runs, so the restatement has to be on the agenda
              ;; or a rule that had not yet reached the original fires on neither.
              _    (when (seq (:superseded mig))
                     (special/refresh-supersessions kb (:superseded mig)))
              ;; A decontextualized predicate is a claim about the predicate, so the lift
              ;; runs on content a rule concluded exactly as it runs on content a caller
              ;; asserted (`assert-one`).  Unconditionally, not only for a new
              ;; conclusion: a re-derivation is how a conclusion that was already
              ;; stored — and so was skipped by the retroactive sweep, or arrived before
              ;; the declaration did — picks its copy up.  The copy is a new datum in a
              ;; context that did not have it, so it is enqueued like the conclusion
              ;; itself.
              lift (special/deduce-lifts kb conseq h pctx)
              ;; The argument constraints entail of a *derived* conclusion exactly what
              ;; they entail of an asserted one.  Drawn only for a new conclusion, like
              ;; the checks above: a re-derivation adds a justification, not content, and
              ;; whatever the sentence entailed was entailed when it was first placed.
              args (merge-with into
                               (special/deduce-arg-types kb (:entailments adm) h pctx)
                               (when new? (special/deduce-below kb conseq h pctx)))
              ;; ...and a conclusion that *is* a declaration reaches back over the stored
              ;; facts, as an asserted one does.
              back (special/entail-existing kb conseq h)
              ;; ...and a derived `genl` edge between predicates brings stored
              ;; sub-predicate facts under the declarations above them, as an asserted
              ;; one does
              down (special/entail-under-edge kb conseq)]
          (when (or (seq (:violations mig)) (seq (:violations lift)) (seq (:violations args))
                    (seq (:violations back)) (seq (:violations down)))
            (violations/report kb (concat (:violations mig) (:violations lift)
                                          (:violations args) (:violations back)
                                          (:violations down))))
          ;; The arms above install the conclusion in its cache unconditionally, and a
          ;; valid firing makes that right.  A void one leaves the node OUT from its
          ;; creation, so no settle's region names it: reconcile its caches here, as
          ;; `recover` does for every stored declaration.
          (when (and forced new?) (special/reconcile-belief-change kb [h]))
          (-> (if new? [h] [])
              (into-some (special/minted-seeds kb (:new mig)))
              (into-some (:new lift))
              (into-some (special/minted-seeds kb (:new args)))
              (into-some (special/minted-seeds kb (:new back)))
              (into-some (special/minted-seeds kb (:new down)))
              ;; a *derived* genl edge makes stored facts matchable at a supertype
              ;; they did not have, exactly as an asserted one does — same seeds, or
              ;; the fixpoint would depend on which rule fired first
              (into-some (special/subsumption-seeds kb conseq))
              ;; and a *derived* link of a transitive predicate extends its answered
              ;; closure exactly as an asserted one does — same seeds, same reason.
              ;;
              ;; **Only for a new conclusion**, unlike the two seed arms either side of
              ;; it, and the asymmetry is the point: those seed facts that cannot
              ;; re-derive the edge which seeded them, so a re-derivation costs a wasted
              ;; pass and converges.  This one seeds the partner triggers of the rules
              ;; joined to the predicate — which are exactly the facts whose rule
              ;; concludes the link, so the datum being processed is itself in the seed
              ;; set it returns.  Ungated, a re-derivation re-seeds its own trigger,
              ;; that trigger re-derives the same pair, and since the agenda in `chain`
              ;; is a plain queue with no dedup the loop never drains: one
              ;; `(parentOf P0 P1)` under a recursive `ancestorOf` runs to
              ;; `max-derivations`.  A re-derivation grew no closure, so there is
              ;; nothing for it to re-drive.
              (into-some (when new? (special/transitive-seeds kb conseq)))
              ;; and a derived genlCx edge widens what a rule can see, for the
              ;; same reason and with the same remedy
              (into-some (special/visibility-seeds kb conseq))))))))

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
  ground reifiable NAT replaced by its constant, as `assert` stores a sentence
  (docs/nat.md), and nil — or the conclusion as far as it could be reified and the
  violation that drops it.

  A NAT that already has a term resolves to it (`nat/reify-existing`: a `rewriteOf`
  target, the value a corresponding predicate names, or the constant a `termOfUnit`
  maps), so a derived sentence and an asserted one naming the same application name one
  constant.  A NAT with no term is minted, which writes premises: its `termOfUnit` map
  and materialized result types, in CxUniverse at `:monotonic`, exactly as `assert`'s
  mint writes them.  The derived conclusion is then one use of the constant, and the
  orphan sweep collects it when the last use goes.

  **The checks run before the mint.**  `violation-of` is the placement's own check list,
  asked of the conclusion under `checks/*entry-mints?*`, which reads an application the
  way the checks read the constant a mint would give it.  A conclusion the checks drop
  therefore mints nothing, and leaves no constant whose only use was never stored.  The
  placement runs its checks again over the reified sentence, as it does for every new
  conclusion; those are the ones that draw the argument-type entailments on the constant.

  A mint is a full assert (`wiring/assert-sentence`) and can refuse.  A firing may not
  throw mid-fixpoint (docs/nmtms.md), so a refused mint becomes the `:mint-refused`
  violation that drops the conclusion, reported like any other.  The mints run under `*defer-settle?*`, for the
  reason a skolem witness's do: the fixpoint settles once when it finishes.

  One walk that allocates nothing is the whole cost for a conclusion naming no reifiable
  NAT (`nat/names-reifiable-nat?`), and two taxonomy-prop reads on a KB declaring no
  reifiable function."
  [kb conseq violation-of]
  (nat/queue-split-uses! kb conseq)
  (if-not (nat/names-reifiable-nat? kb conseq)
    [conseq nil]
    (let [known (nat/reify-existing kb conseq)]
      (if-not (nat/names-reifiable-nat? kb known)
        [known nil]
        (if-let [v (binding [checks/*entry-mints?* true] (violation-of known))]
          [known v]
          (try
            [(binding [wiring/*defer-settle?* true] (nat/maybe-reify-nats kb known)) nil]
            (catch clojure.lang.ExceptionInfo e
              (if (get (ex-data e) :type)
                [known (mint-violation e)]
                (throw e)))))))))

(defn- place-conclusion
  "Place one firing's conclusion, whatever kind of thing it is.

  A conclusion that **is a rule** is a generator's mint (`mint-rule`,
  docs/generators.md); everything else is a fact (`place-fact-conclusion`).  The split
  is here rather than at the call sites because both of them — a fresh firing and a
  released refusal — must make it the same way, and because every arm of the fact path
  is about a fact: argument types, the functional merge, the decontextualized lift,
  subsumption seeds.  None of them means anything said of a rule.

  Before the split, every ground reifiable NAT in the conclusion is reified to its
  constant (`reify-conclusion`), so both arms store the sentence `assert` would store and
  a derived use of an application names the constant an asserted one names.

  `all-antes` is the firing's antecedent handles **in whatever order the caller holds
  them**; both arms sort it by content (`kb/antecedent-order`) at the point they write a
  justification, and neither reads a position before that.  A released refusal hands over
  a vector that is already sorted, which the sort returns unchanged — the key is a
  function of the handle, so re-sorting is idempotent.  `subs` is the firing's
  subsumptions, the set of its `subsumption-links` or nil, which the justification
  records."
  [kb rule conseq pctx all-antes depth bindings strength subs]
  (let [rule?  (rules/rule-sentence? (peek (sx/peel-rule-wrapper conseq)))
        [c v]  (reify-conclusion kb conseq
                                 (if rule?
                                   #(stamped-rule-violation kb % pctx)
                                   #(fact-violation kb rule % pctx (checks/constraint-admission kb % pctx))))]
    (cond
      (and v rule?) (do (violations/report kb [(assoc v :sentence (stamped-rule c) :context pctx
                                                      :rule (:rule-handle rule))])
                        [])
      v             (drop-fact-conclusion! kb rule c pctx all-antes bindings subs v)
      rule?         (mint-rule kb rule c pctx all-antes depth bindings strength subs)
      :else         (place-fact-conclusion kb rule c pctx all-antes depth bindings strength subs))))

(defn- placement-ingredients
  "Where a firing's conclusion may live, and which taxonomy supporters it names getting
  there: `[placement-contexts {placement-context [edge-handle]}]`.  Both relations are
  in that handle list — the `genl` edges the match subsumed through, and the `genlCx`
  edges the placement sees its ingredients over.

  The placement is derived from the firing's three ingredients — the rule, the
  antecedent facts, and the taxonomy the match climbed — by the one rule that has always
  governed the first two: the **maximal contexts that see all of them**.  The edges enter
  that computation as their supporters' asserting contexts.

  They are chosen to **constrain the placement least**, which is what makes this a
  widening of the rule for the rule and the facts alone rather than a different one.
  Where a maximal context seeing the rule and the facts can also see a path, the edges
  add no constraint at all and the placement is exactly what it would have been —
  per candidate, since two incomparable candidates may see different supporters of one
  edge, and picking one witness for both would drop whichever candidate cannot see it.
  Only where a candidate sees no path is the taxonomy a binding constraint, and then the
  conclusion descends to the maximal contexts that see the edges too rather than landing
  in a `:no-placement`.  A supporter with no recorded context is seen from
  everywhere and constrains nothing, so it drops out of the list rather than emptying it.

  The descent places the conclusion once per witness combination no other covers
  (`descent-placements`), so two routes stated in sibling contexts each place it below
  their own context.  Where *some* candidates see a path and others do not, the ones that
  see keep their placement, and the descent adds the placements that are not at or below
  one of them."
  [kb rule links fact-handles fact-ctxs]
  (placements-over kb links (cons (:rule-handle rule) fact-handles) (cons (:context rule) fact-ctxs)))

;; ---- the families that place their nogoods -----------------------------

(defn- route-supporters
  "Each choice of one believed supporter per flat-cache key of `ks`, as a vector of
  `[handle context]`."
  [kb ks]
  (let [tax  (reasoning/taxonomy kb)
        tms  (reasoning/tms kb)
        recs (:records kb)]
    (reduce (fn [acc k]
              (let [hs (sort (filter #(jtms/in? tms %) (tax/visible-supporters tax k nil)))]
                (for [xs acc, h hs] (conj xs [h (:context (p/get-sentex recs h))]))))
            [[]] ks)))

(defn- route-placements
  "The `[context antecedents]` placements of the nogood over `members` that the `routes`
  give (`membership/routes`, `related/routes`, `tuple/routes`): for each route and each
  choice of one believed supporter per key it reads, or each of its `:choices` of
  `[handle context]` supporters, each context `placements-over` places the members,
  those supporters and the route's subsumptions at, with the members, the supporters and
  the edge handles it names as antecedents.  A placement that reads a
  `siblingDisjointException` exempting a mark route's separated pair is left out
  (`tax/route-exempted?`), and so is one the route's `:excluded-at` names."
  [kb members routes]
  (let [tax   (reasoning/taxonomy kb)
        recs  (:records kb)
        exc?  (tax/sib-exceptions? tax)
        mctxs (mapv #(:context (p/get-sentex recs %)) members)]
    (into #{}
          (for [{:keys [keys links choices excluded-at] :as route} routes
                sups (or choices (route-supporters kb keys))
                :let [[ps m] (placements-over kb links (into (vec members) (map first) sups)
                                              (into mctxs (map second) sups))]
                pctx ps
                :when (not (and exc? (tax/route-exempted? tax route pctx)))
                :when (not (and excluded-at (excluded-at pctx)))]
            [pctx (-> (set members) (into (map first) sups) (into (get m pctx)))]))))

(defn- content-key
  "The content order of a nogood's member set: each member's sentence and context, sorted."
  [kb ms]
  (sort nm/compare-form (map #(let [s (p/get-sentex (:records kb) %)] [(:sentence s) (:context s)]) ms)))

(defn- place-sets!
  "Place each nogood of `ngs` whose members are all IN in the network
  (`jtms/network-in?`) at the placements its `routes-of` gives, and remove the
  placements of each member set of `stale`, each under `owns?` (`place-justified!`), in
  content order.  Returns the handles created."
  [kb ngs stale routes-of owns?]
  (let [tms (reasoning/tms kb)]
    (-> []
        (into (mapcat #(place-justified! kb % [] (fn [core] (owns? % core))))
              (nm/sort-by-content-key #(content-key kb %) nm/compare-form stale))
        (into (comp (filter (fn [ng] (every? #(jtms/network-in? tms %) (:members ng))))
                    (mapcat (fn [{ms :members :as ng}]
                              (place-justified! kb ms (route-placements kb ms (routes-of ng))
                                                (fn [core] (owns? ms core))))))
              (nm/sort-by-content-key #(content-key kb (:members %)) nm/compare-form ngs)))))

(defn- stale-sets
  "The member sets of the nogoods placed over a handle of `hs` that `kind-of` names and
  `current`, a set of member sets, does not hold."
  [kb hs kind-of current]
  (let [recs (:records kb)]
    (into #{} (comp (mapcat #(placed-justifications kb %))
                    (map :members)
                    (remove current)
                    (filter #(kind-of recs %)))
          hs)))

(defn- reach-handles
  "What a `genlCx` move `reach` (`decide/edge-reach`) can give or take a placement through,
  `[handles grounds]`: the candidates (`decide/handles-at`) stated in a context of its
  `:below`, and the handles stated in the contexts of `:below` that state a `genl` edge or
  a declaration (`tax/asserting-contexts-among`, read by context with
  `reads/as-stored-in-context`), whose grounds reach nogoods over the types below them
  (`ground-ends`).  nil when `reach` is, `::all` when the relation was rebuilt."
  [kb c reach]
  (cond
    (nil? reach)  nil
    (:all? reach) ::all
    :else
    (let [tax (reasoning/taxonomy kb)
          bl  (:below reach)]
      [(set (when (seq bl) (decide/handles-at c bl)))
       (into [] (mapcat #(reads/as-stored-in-context (:index kb) %))
             (filter (tax/asserting-contexts-among tax bl) bl))])))

(defn- genl-lower-ends
  "The lower end of each `genl` edge stated by a handle of `hs`."
  [kb hs]
  (let [recs (:records kb)]
    (into #{} (keep (fn [h] (let [s (:sentence (p/get-sentex recs h))]
                              (when (and (seq? s) (= 'genl (first s)) (= 3 (count s))
                                         (symbol? (second s)))
                                (second s)))))
          hs)))

(defn- ground-ends
  "The types the grounds among the handles `hs` reach a membership nogood under: the
  lower end of a stated `genl` edge, and the ends of a separation or cover declaration's
  flat-cache keys (`tax/separation-ends`)."
  [kb hs]
  (let [tax (reasoning/taxonomy kb)]
    (into (into #{} (comp (keep #(tax/separation-ends tax %)) cat) (tax/supported-keys tax hs))
          (genl-lower-ends kb hs))))

(defn- mark-ends
  "The predicates the grounds among the handles `hs` reach a tuple nogood under: the lower
  end of a stated `genl` edge with a mark at or above it (`tuple/under-mark?`), and the
  predicate a mark's flat-cache key names (`tuple/owned?`'s keys)."
  [kb hs]
  (let [tax (reasoning/taxonomy kb)]
    (into (into #{} (keep (fn [[kind a b]] (case kind :prop b :functional-in-arg a nil)))
                (tax/supported-keys tax hs))
          (filter #(tuple/under-mark? tax %))
          (genl-lower-ends kb hs))))

(defn- place-memberships!
  "Place the membership nogoods whose placement can have moved, and remove the placements
  of those gone, and return the handles created: the nogoods of the terms `moved` names
  (`membership/take-moved!`), of the terms with a membership or denial among the handles
  `fresh` the pass relabelled or `placed` (`placed-members`), of the terms holding a type
  under a separation or cover declaration among `fresh` (`membership/terms-under`), and
  of the terms with a candidate a `genlCx` move reaches or a type under a ground stated
  where it reaches (`reach-handles` over `reach`, `ground-ends`).
  Each is placed at the placements its routes give (`membership/routes`,
  `route-placements`).  Reads nothing while the index keeps no nogood and queued none."
  [kb c moved reach fresh placed]
  (when (or (seq moved) (seq (membership/nogoods-terms c)))
    (let [tax  (reasoning/taxonomy kb)
          recs (:records kb)
          w    (decide/write-view tax)
          rh   (reach-handles kb c reach)
          xs   (-> (set (keys moved))
                   (into (membership/terms-of kb c fresh))
                   (into (membership/terms-of kb c placed))
                   (into (membership/terms-under w c (into #{} (comp (keep #(tax/separation-ends tax %)) cat)
                                                           (tax/supported-keys tax fresh))))
                   (into (if (= ::all rh)
                           (membership/nogoods-terms c)
                           (let [[hs gs] rh]
                             (cond-> (membership/terms-of kb c hs)
                               (seq gs) (into (membership/terms-under w c (ground-ends kb gs))))))))]
      (into []
            (mapcat (fn [x]
                      (let [ngs (membership/nogoods-of c x)
                            hs  (into (set (get moved x)) (mapcat :members) ngs)]
                        (place-sets! kb ngs
                                     (stale-sets kb hs membership/kind-of (into #{} (map :members) ngs))
                                     #(membership/routes w recs %)
                                     #(membership-owned? kb %1 %2)))))
            (sort xs)))))

(defn- place-related!
  "Place the related-types nogoods whose placement can have moved, and remove the
  placements of those gone, and return the handles created: the nogoods holding a
  declaration `moved` names (`related/take-moved!`) or the pass relabelled (`fresh`) or a
  relabelled placement of the family names (`placed`, member sets), each contradicted `orthogonal` with an argument
  at or below a type a separation declaration among `fresh` names
  (`related/reread-separated!`), those holding a candidate a `genlCx` move reaches, and
  every one when a ground is stated where the move reaches (`reach-handles` over
  `reach`): the family's nogoods are its declarations over related types, which are few.
  Each is placed at the placements its routes give (`related/routes`,
  `route-placements`)."
  [kb c moved reach fresh placed]
  (let [holds? (:holds? related/family)
        tax    (reasoning/taxonomy kb)
        recs   (:records kb)
        w      (decide/write-view tax)
        ends   (into #{} (comp (keep #(tax/separation-ends tax %)) cat) (tax/supported-keys tax fresh))
        sep    (related/reread-separated! kb w ends)
        c      (if (seq sep) (decide/synced kb) c)
        rh     (reach-handles kb c reach)
        hs     (-> (set moved)
                   (into (filter #(holds? c %)) fresh)
                   (into (comp (filter #(related/kind-of w recs %)) cat) placed)
                   (into sep)
                   (into (cond
                           (nil? rh)         nil
                           (= ::all rh)      ((:handles related/family) c)
                           (seq (second rh)) ((:handles related/family) c)
                           :else             (filter #(holds? c %) (first rh)))))]
    (when (seq hs)
      (let [ngs (into #{} (mapcat #(related/nogoods-holding c %)) hs)]
        (place-sets! kb ngs
                     (stale-sets kb hs #(related/kind-of w %1 %2) (into #{} (map :members) ngs))
                     #(related/routes w recs %)
                     (fn [ms _] (boolean (related/kind-of w recs ms))))))))

(defn- place-tuples!
  "Place the tuple nogoods whose placement can have moved, and remove the placements of
  those gone, and return the handles created: the nogoods holding a member `moved` names
  (`tuple/take-moved!`), a member the pass relabelled (`fresh`) or a relabelled placement
  names (`placed`), a member under a mark or a `genl` edge among `fresh`
  (`tuple/members-under`, `mark-ends`), and a member a `genlCx` move reaches or under a
  ground stated where it reaches (`reach-handles` over `reach`, and the self tuples stated
  there, `tuple/self-tuples-in`).  Each is placed at the placements its routes give
  (`tuple/routes`, `route-placements`).  Reads nothing while the index keeps no member,
  no `irreflexive` mark is stored and nothing is queued."
  [kb c moved reach fresh placed]
  (when (or (seq moved) (tuple/held? (reasoning/taxonomy kb) c))
    (let [tax  (reasoning/taxonomy kb)
          w    (decide/write-view tax)
          rh   (reach-handles kb c reach)
          mem? #(tuple/member? kb c %)
          hs   (-> (set moved)
                   (into (filter mem?) fresh)
                   (into (filter mem?) placed)
                   (into (tuple/members-under kb w c (mark-ends kb fresh)))
                   (into (cond
                           (nil? rh)    nil
                           (= ::all rh) (tuple/members kb w c)
                           :else        (let [[hs gs] rh]
                                          (-> (filterv mem? hs)
                                              (into (tuple/self-tuples-in kb w (:below reach)))
                                              (into (tuple/members-under kb w c (mark-ends kb gs))))))))]
      (when (seq hs)
        (let [ngs (tuple/nogoods-holding kb c hs)]
          (place-sets! kb ngs
                       (stale-sets kb hs (constantly true) (into #{} (map :members) ngs))
                       #(tuple/routes kb w c %)
                       (fn [ms core] (tuple/owned? tax ms core))))))))

(defn- place-arities!
  "Place the arity nogoods whose placement can have moved, and remove the placements of
  those gone, and return the handles created: the nogoods holding a handle `moved` names
  (`arity/take-moved!`), a candidate or a binding the pass relabelled (`fresh`) or a
  relabelled placement names (`placed`), a candidate under a `genl` edge among `fresh`
  (`arity/members-under`), and a candidate a `genlCx` move reaches, under a ground stated
  where it reaches, or convicted by a binding stated there (`reach-handles` over `reach`,
  `arity/reached`).  Each is placed at the placements its routes give (`arity/routes`,
  `route-placements`).  Reads nothing while the index keeps no candidate and queued
  nothing."
  [kb c moved reach fresh placed]
  (when (or (seq moved) (arity/held? c))
    (let [tax  (reasoning/taxonomy kb)
          w    (decide/write-view tax)
          rh   (reach-handles kb c reach)
          mem? #(arity/member? c %)
          hs   (-> (set moved)
                   (into (filter mem?) fresh)
                   (into (filter mem?) placed)
                   (into (arity/members-under kb w c (genl-lower-ends kb fresh)))
                   (into (cond
                           (nil? rh)    nil
                           (= ::all rh) ((:handles arity/family) c)
                           :else        (let [[hs gs] rh]
                                          (-> (filterv mem? hs)
                                              (into (arity/members-under kb w c (genl-lower-ends kb gs)))
                                              (into (arity/reached kb w c (:below reach))))))))]
      (when (seq hs)
        (let [ngs (arity/nogoods-holding kb w c hs)]
          (place-sets! kb ngs
                       (stale-sets kb hs (constantly true) (into #{} (map :members) ngs))
                       #(arity/routes kb w c % (fn [h] (exc/closure-excepted-anywhere? kb h)))
                       (fn [ms core] (arity/owned? kb ms core))))))))

(defn placement-queued?
  "Has the negation, membership, related-types, tuple or arity index queued a nogood the
  settle places again (`negation/take-moved!`, `membership/take-moved!`,
  `related/take-moved!`, `tuple/take-moved!`, `arity/take-moved!`)?  A rebuilt index
  queues every standing one (`recover`).  The negation family keeps no candidate rows:
  after a rebuild every pair is owed while a body is stored in both polarities
  (`decide/placements-owed?`, `reads/stores-opposed?`)."
  [kb]
  (let [c (decide/synced kb)]
    (or (negation/moved? c)
        (and (decide/placements-owed? c) (reads/stores-opposed? (:index kb)))
        (membership/moved? c) (related/moved? c) (tuple/moved? c) (arity/moved? c))))

(defn place-inherited!
  "Find the inherited clashes (`discovery/discover-inherited!`) and place each found one
  at its vantages, the most general contexts that read it whole, justified by its members
  (the stored claim and the reading's reasons) and the `genlCx` edges each vantage sees
  them over, and remove the placements of each member set no longer found
  (`place-justified!`), in content order.  Returns the handles created.  A clash whose
  memo entry was carried keeps its placements.  A rebuild's settle places too
  (docs/nmtms.md, \"A `recover` places the nogoods its store does not hold\")."
  [kb region]
  (let [{:keys [found left]} (discovery/discover-inherited! kb region)
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
  placement can have moved since the last call, and return the handles created: the
  negation pairs (`place-negations!`), the membership nogoods (`place-memberships!`), the
  related-types nogoods (`place-related!`), the tuple nogoods (`place-tuples!`) and the
  arity nogoods (`place-arities!`).  Every family detects over the network's IN label, a
  superseded member included (`jtms/network-in?`), so a supersession moves no placement.
  Each family reads what its write-time index queued, the handles among `region` (a delay)
  relabelled that `read` (a volatile set) does not hold yet, which this adds, the handles
  an except of which arrived or left and what rests on them, the placed `contradicts`
  among them, and the `genlCx` edges moved since (`decide/edge-reach`).  Reads nothing
  while no family holds a nogood or queued one and no `orthogonal` is stored."
  [kb region read]
  (let [c (decide/synced kb)
        bodies (negation/take-moved! kb)
        [since first?] (decide/take-edge-cursor! kb)
        mmoved (membership/take-moved! kb)
        rmoved (related/take-moved! kb)
        tax    (reasoning/taxonomy kb)
        ;; a family that keeps no nogood places nothing, and a queued handle then matters
        ;; only for the placements it holds, which the family removes
        tms     (reasoning/tms kb)
        holds?  (fn [h] (some #(= nogood-informant (:informant (jtms/justification tms %)))
                              (jtms/dependents tms h)))
        placing (fn [held? moved] (if held? moved (into #{} (filter holds?) moved)))
        tmoved (placing (tuple/held? tax c) (tuple/take-moved! kb))
        amoved (placing (arity/held? c) (arity/take-moved! kb))]
    (when (or (reads/stores-opposed? (:index kb)) (seq mmoved) (seq (membership/nogoods-terms c))
              (seq rmoved) (seq ((:handles related/family) c))
              (related/orthogonals? kb (decide/write-view tax))
              (seq tmoved) (tuple/held? tax c) (seq amoved) (arity/held? c))
      (let [fresh  (into [] (comp (distinct) (remove @read)) @region)
            _      (vswap! read into fresh)
            ;; an except arriving or leaving moves a placement with no relabel of the
            ;; handle it names or of what rests on it (`special/except-moved`, its
            ;; consequence closure), drained once a pass
            fresh  (into fresh (remove (set fresh))
                         (jtms/consequence-closure (reasoning/tms kb) (special/except-moved kb)))
            psets  (placed-members kb fresh)
            placed (into #{} cat psets)
            reach  (when since (decide/edge-reach tax since))
            made   (-> []
                       (into (place-negations! kb bodies reach first? fresh placed))
                       (into (place-memberships! kb c mmoved reach fresh placed))
                       (into (place-related! kb c rmoved reach fresh psets))
                       (into (place-tuples! kb c tmoved reach fresh placed))
                       (into (place-arities! kb c amoved reach fresh placed)))]
        ;; a placement this pass created is relabelled by its creation alone, so the next
        ;; pass does not read it as moved and place its nogood again
        (vswap! read into made)
        made))))

;; ---- a refused firing is remembered as bindings --------------------------
;;
(defn- refusal-reason
  "Why a completed firing may not be placed in `pctx`, or nil — `:post-join`,
  `:exception`, `:naf` or `:hidden`, in the order they are cheapest to decide.  A
  closed-extent negative antecedent that does not hold reports `:naf`, which is what it
  is: the same undercutting block, recorded in the same refusal record, released by the
  same re-evaluation.

  Reading the rule *view* rather than the record: `:excepts` and `:naf` are already in
  hand on the firing path, and fetching them again per firing is what the view exists to
  avoid.  `bindings` is nil when a post-join literal had no answer, or more than one."
  [kb rule antes bindings pctx]
  (cond
    (nil? bindings)                                                 :post-join
    (some #(and (provers/exception-visible-from? kb pctx %)
                (exception-holds? kb (:query %) bindings pctx))
          (:excepts rule))                                          :exception
    (naf-blocks? kb (:naf rule) bindings pctx)                       :naf
    (closed-extent-blocks? kb (:closed-extent rule) bindings pctx)   :naf
    (antecedent-hidden? kb antes pctx)                               :hidden))

(def ^:dynamic *report-no-placement?*
  "Whether a completed firing that finds no placement context files a `:no-placement`
  entry.  True wherever content arrives, which is every path a caller drives: a firing
  that did everything but conclude is silent otherwise, and it is the commonest
  first-session mistake.

  **False for the re-chain a teardown owes** (`core/settle-after-teardown!`).  That pass
  re-asks firings the removal already swept, to learn which of them a surviving route
  still licenses — so one it cannot place is a restatement of the retraction rather than a
  diagnosis of the KB, and the caller who took the wiring away is the last person who
  needs telling.  Filing one per killed firing would also cost the ledger its real
  entries, which cap at 1000, and a `:warn` line apiece."
  true)

(defn- placement-antecedents
  "The antecedents a firing's placement reads, as `[handles records]`: all of `handles`
  (with `facts`, their records) but a permuting-mark statement the firing names without
  having matched it — the mark a fact read in another argument order rests on
  (`read-marks`), or the one a mirrored claim names (`inherit/claim-supports`).

  A permuting mark decides the key a sentex is stored under, and a sentex has one key
  for every context, so the matcher reads the mark from every context whether or not
  one sees a statement of it.  A firing names the mark so retracting it withdraws the
  firing, and it is placed where the rule and the facts it matched allow, as the same
  firing over a fact stored in the order the rule reads it is.  Placed by the mark's
  context as well, a firing in a context that sees no statement of the mark — one with
  no `genlCx` edge, or one above CxUniverse — would find no placement when the mark
  arrives first, and would keep the firing it made before the mark when the mark arrives
  last.

  A mark statement the rule matched as an antecedent is a matched fact like any other,
  and places the firing.  A firing naming no permuting mark gets its inputs back."
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

(defn- place-conseq
  "Place one ground conclusion literal `raw-c` from a firing: resolve its placement
  contexts — the maximal contexts that see the rule and all antecedent facts — and
  place it in each unless the rule's exception or a
  NAF antecedent blocks it there.  Returns the newly created handles.  A firing with no
  placement context is recorded like any other dropped conclusion, and one refused by a
  re-checkable block condition is recorded as a refusal (see above).

  `links` are the firing's subsumptions (`subsumption-links`); the `genl` supporters
  witnessing them are an **ingredient of the placement** (`placement-ingredients`), not
  a filter on it, and they join the antecedent list.  So do the `genlCx` supporters
  the placement sees its ingredients over: a placement is a claim about the ancestor set, and
  the conclusion may not outlive the edges that claim rests on.

  `placed` is `[handles records]` of the antecedents the placement reads
  (`placement-antecedents`); `handles` is all of them, which a refusal records so its
  release computes the depth a fresh firing would."
  [kb rule conseq handles placed all-antes links depth max-depth bindings]
  (let [[phs facts]          placed
        subs                 (when (seq links) (set links))
        fact-ctxs            (map :context facts)
        [placements support] (placement-ingredients kb rule links phs fact-ctxs)]
    (if (empty? placements)
      ;; The join completed — every antecedent matched — and then the conclusion
      ;; evaporated: no context sees everything the firing rests on (sibling
      ;; contexts with no common descendant, the taxonomy it climbed included).
      ;; "Possibly none" is a legitimate outcome of
      ;; maximal-common-descendant-contexts, but a silent one reads as "the rule fired",
      ;; so it is recorded like any other dropped conclusion — naming the subsumption
      ;; when there was one, since "your context cannot see that genl edge" is a
      ;; different thing to go and fix from "your facts are in sibling contexts".  The
      ;; contexts that *would* have taken it but for the edges are recomputed here, on
      ;; the drop path only, because that difference is the whole diagnosis.
      ;; ...unless the pass is a teardown's re-chain, which is asking rather than being
      ;; told: `*report-no-placement?*` says why.
      (do (when *report-no-placement?*
            (violations/report kb
                               [{:violation :no-placement :sentence conseq :rule (:rule-handle rule)
                                 :detail (cond-> {:rule-context  (:context rule)
                                                  :fact-contexts (vec (distinct fact-ctxs))
                                                  :message
                                                  ;; the remedy, not only the diagnosis: this
                                                  ;; fires on the commonest first-session
                                                  ;; mistake — facts asserted into a context
                                                  ;; with no edge to the one holding the rule
                                                  ;; — where the reader has a rule that did
                                                  ;; everything but conclude, and a message
                                                  ;; that named the shortfall without naming
                                                  ;; the relation that closes it
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
      ;; `exceptWhen`, `unknown`, and a visibility `except` all **block**: for a
      ;; placement one of whose exceptions holds, one of whose `(unknown S)` antecedents
      ;; finds `S` derivable, or one of whose antecedent facts a believed `except` hides
      ;; from the placement context, there is no conclusion and no justification —
      ;; nothing to defeat and nothing to arbitrate.  The check is per *placement*,
      ;; because all three are evaluated in the conclusion's context and a firing may
      ;; place into several.  `all-antes` includes the rule handle, which the hidden
      ;; set matches on purpose: a hidden rule may not fire into the ancestor set any more
      ;; than a hidden fact may support a firing there.
      ;; `mapcat`, not `map`: one placement yields the conclusion *and* a copy in each
      ;; context the predicate is lifted into, and every one of them is a new datum the
      ;; agenda has to see.
      (into []
            (mapcat (fn [pctx]
                      ;; the taxonomy supporters — `genl` and `genlCx` alike — are per
                      ;; placement, so the antecedent list
                      ;; is too — and it is this list, not `all-antes`, that the `except`
                      ;; check reads, since `justification-excepted?` re-runs that check
                      ;; over the *stored* justification's antecedents and the two must
                      ;; not disagree about what the firing rests on.
                      ;;
                      ;; **Arrival order here, content order at the point of storing.**
                      ;; The stored vector must be `kb/antecedent-order`'s — the join
                      ;; yields its handles in trigger order, which is the agenda's, so
                      ;; every report that reads a stored justification would otherwise
                      ;; say which side arrived first.  But that order is bought with a
                      ;; printed sentence per antecedent, and nothing between here and
                      ;; the store reads a position: `refusal-reason` reaches the list
                      ;; only through `antecedent-hidden?`, which is a `some` over it,
                      ;; and the dedup below it is set-keyed (`jtms/has-justification?`).
                      ;; So the sort moves to the two places that keep something — the
                      ;; refusal record here, the justification in `place-conclusion` —
                      ;; and a firing that is refused outright or that re-derives a
                      ;; conclusion over support already justifying it stops paying for a
                      ;; vector it throws away.  How many firings that is depends on the
                      ;; rule set and can be none: a self-joining transitive closure
                      ;; reaches each pair by a different intermediate, so every one of
                      ;; its firings is a distinct justification and stores.
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
                          (when (or (= :exception why) (= :naf why))
                            ;; a refusal entry is content the ledger keeps and
                            ;; deduplicates by value, and `release-refusal!` hands its
                            ;; `:antes` straight to `place-conclusion` — so it is
                            ;; ordered here, exactly as a stored justification is
                            (record-refusal! kb rule c pctx (kb/antecedent-order kb antes)
                                             handles bindings max-depth
                                             (when subs {:subsumptions subs}))
                            nil)
                          (place-conclusion kb rule c pctx antes depth bindings
                                            (:strength rule) subs)))))
            placements))))

(defn- derive-conclusion
  "Record one rule firing at the rule's own justification strength (`:strength` on the
  rule view, `provers/firing-strength`).  The justification is placed
  in the *maximal* contexts that see the rule and all antecedent facts (via
  genlCx); returns {:new [handles]} for any newly created sentexes.  The rule
  handle is part of the justification, so retracting the rule retracts its
  justifications.  A default conclusion is placed *unconditionally* — any defeat is
  decided at settle time, so belief is order-independent.

  A **head existential** `(exists ?y C)` leaves `?y` unbound after the antecedent
  substitution, and it is skolemized here, before placement (docs/skolem.md)."
  [kb rule {:keys [bindings handles matched]} max-depth truncated]
  (let [tms   (reasoning/tms kb)
        depth (inc (long (reduce (fn [d h] (max (long d) (long (jtms/depth tms h)))) 0 handles)))]
    (if (> depth max-depth)
      (do (reset! truncated true) (when *tick* (*tick* 0)) {:new []})
      (let [raw0      (res/substitute (:consequent rule) bindings)
            ;; existential head variables are exactly the ones still unbound here, less
            ;; a post-join literal's output (computed per placement, a count and not a
            ;; witness).  A generator's head is not skolemized: the variables of the
            ;; rule it stamps are that rule's own (docs/generators.md).
            free      (when-not (rules/rule-sentence? (peek (sx/peel-rule-wrapper raw0)))
                        (let [f (free-consequent-vars raw0)]
                          (if-let [post (seq (:post-join rule))]
                            (seq (remove (into #{} (mapcat sx/deferred-output-vars) post) f))
                            f)))
            raw       (if free (skolem/skolemize-conclusion kb rule raw0 bindings free) raw0)
            ;; a ground `(Quasiquote T)` in the fired head constructs its `(Quote E)`
            ;; mention here, and the placement's reify pass (`reify-conclusion`) mints
            ;; it — a no-op unless quasiquotation is declared
            ;; (`quasiquote/any-quasiquote?`, the `(quoting_function Quasiquote)` gate)
            raw       (quasiquote/maybe-reduce kb raw)
            ;; a conjunctive skolemized head shares one witness across its conjuncts
            ;; (only a head existential stores a conjunctive consequent — an ordinary
            ;; one is split by `expand-consequent` before storage)
            conjuncts (if (and (sequential? raw) (= sx/and-functor (first raw)))
                        (vec (rest raw)) [raw])
            all-antes (conj (vec handles) (:rule-handle rule))
            ;; the matched records, fetched once: placement reads their contexts, and
            ;; the subsumption links read their antecedent keys
            facts     (mapv #(p/get-sentex (:records kb) %) handles)
            ;; a handle's record, read off the two aligned vectors: a firing has a
            ;; handful of antecedents, and a map built per firing to look them up
            ;; costs more than scanning them
            record-of (fn [h] (loop [i 0]
                                (when (< i (count facts))
                                  (if (= h (nth handles i)) (nth facts i) (recur (inc i))))))
            links     (subsumption-links kb matched record-of)
            placed    (placement-antecedents handles facts matched)
            new       (reduce (fn [acc c]
                                (into acc (place-conseq kb rule c handles placed all-antes links
                                                        depth max-depth bindings)))
                              [] conjuncts)]
        ;; a firing is the finest unit of work the fixpoint has, so it is where a long
        ;; datum reports from — including a firing that placed nothing, since a join
        ;; grinding through matches that all turn out blocked is exactly the stretch that
        ;; otherwise looks hung
        (when *tick* (*tick* (count new)))
        ;; a placed preservation declaration changes what every later join may inherit
        (note-placed-declaration! conjuncts)
        {:new new}))))

(defn rule-view-of
  "The chainer's view of a rule sentex.  `:strength` is the justification class its
  firings confer (`provers/firing-strength`)."
  [kb handle rsx]
  (let [antes    (:antecedent rsx)
        watched? (reads/watched-rule? (:index kb) handle)]
    {:name handle :rule-handle handle :context (:context rsx)
     :antecedents antes :consequent (:consequent rsx) :watched? watched?
     :strength (provers/firing-strength kb handle rsx watched? nil)
     ;; the `exceptWhen` exceptions — `{:context :query}` per believed meta-sentex
     ;; naming this rule, block-if-any (`provers/rule-exception-entries`).  The context
     ;; stays with each query because a placement context reads only the exceptions it
     ;; sees.  Fetched only when the cheap roster gate says the rule is watched, so an
     ;; ordinary firing pays nothing (docs/exceptions.md).
     :excepts (when watched? (provers/rule-exception-entries kb handle))
     ;; the negation-as-failure antecedents — `(unknown S)` literals, blocked the same
     ;; way an exception is, per placement context (docs/naf.md)
     :naf (rules/naf-antecedents rsx)
     ;; ...and the negative antecedents a `closed_extent_predicate` grant reads as NAF —
     ;; withheld from the join and decided here, for the same reason and by the same
     ;; block/sweep/revive path (docs/naf.md)
     :closed-extent (closed-extent-antecedents kb antes)
     ;; the aggregates and what reads their output, which run per placement
     :post-join (rules/post-join-antecedents rsx)}))

(defn- rule-view [kb handle]
  (rule-view-of kb handle (p/get-sentex (:records kb) handle)))

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
                 (-> (if (empty? cur') (dissoc m rh) (assoc m rh cur'))
                     (special/drop-kinds rh [entry])))
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
  longer a firing to make, `:blocked` when the condition that refused it still holds,
  `:free` when it does not and the conclusion is owed a placement.

  Nothing remembers the previous answer — the record says which firings to re-ask and
  never what the answer is, exactly as `exception-blocked-set` re-decides every
  candidate justification it looks at.  Blocking would otherwise drift from belief.

  The judgement is `rule-firing-blocked?`, the same one a placed firing's justification
  is re-decided by, plus the visibility `except` check the justification path also runs.
  Bindings are settled to the representatives `pctx` now elects first, for the reason
  `settled-bindings` records: a snapshot asks about a spelling a merge has retired, and
  the empty result that comes back reads as *not excepted*."
  [kb rh entry]
  (let [rsx (p/get-sentex (:records kb) rh)]
    (if-not (refusal-live? kb rsx entry)
      :dead
      (let [pctx (:pctx entry)]
        (cond
          ;; a dropped argument conviction is re-decided by the check that dropped it
          (:constraint entry)
          (if (:violation (checks/constraint-admission kb (:conseq entry) pctx)) :blocked :free)

          (or (antecedent-hidden? kb (:antes entry) pctx)
              (rule-firing-blocked? kb rh rsx
                                    (delay (settled-bindings kb (:bindings entry) pctx))
                                    pctx))
          :blocked

          :else :free)))))

(defn- restamp-refusal!
  "Replace `:constraint` entry `entry` of rule `rh` with the same entry decided under
  generations `gens` and watching `watch`: the conviction was re-asked and still holds,
  so the next re-ask is owed only once the generations move again or a membership of
  the term the conviction **now** names moves.  A no-op when the entry has already
  left."
  [kb rh entry gens watch]
  (swap! (reasoning/refused kb)
         (fn [m]
           (let [cur (get m rh)]
             (if (and (set? cur) (contains? cur entry))
               (assoc m rh (conj (disj cur entry) (merge entry {:gens gens} watch)))
               m)))))

(defn redecide-constraint-refusal!
  "Re-ask `:constraint` entry `entry` of rule `rh` under generations `gens`: `:free` when
  the conviction no longer holds and the conclusion is owed a placement, nil otherwise.
  An entry whose firing has left is retired.  One still convicted is restamped with
  `gens` and with the term of the conviction read now (`checks/conviction-watch`), not
  the term it was recorded with, so the entry is re-asked when the argument it is
  convicted on is lifted, whichever argument that has become.  The term is read by
  `checks/conviction-watch`, the reader `record-constraint-drop!` records with, so the
  restamped entry watches the term a firing refused now would record — which is what a
  `recover` that rebuilds the record by re-firing records."
  [kb rh entry gens]
  (let [rsx (p/get-sentex (:records kb) rh)]
    (if-not (refusal-live? kb rsx entry)
      (do (drop-refusal! kb rh entry) nil)
      (if-let [v (:violation (checks/constraint-admission kb (:conseq entry) (:pctx entry)))]
        (do (restamp-refusal! kb rh entry gens (checks/conviction-watch v)) nil)
        :free))))

(defn constraint-refusals
  "Every `:constraint` entry in the refusal record, as `[rule-handle entry]` pairs, sorted
  on the rule handle and then on the conclusion and its context, read off the rules the
  kind roster names (`special/kind-entries`).  Each entry is re-asked on its own, so
  the order decides no placement."
  [kb]
  (->> (special/kind-entries @(reasoning/refused kb) :constraint)
       (sort-by (fn [[rh e]] [rh (nm/print-key (:conseq e)) (nm/name-key (:pctx e))]))
       vec))

(defn rule-firing-report
  "Per forward rule in the KB, what it did with itself: how many firings it **placed**,
  how many it **refused** and why, or whether it did nothing at all.  The read behind the
  chaining funnel (docs/web.md) — the ontological engineer's *which of my rules actually
  do anything*.

  Rules are enumerated off the antecedent roster (`:rule-antecedents`) unioned through the
  rule index, so this costs `O(rules)`, never a scan of the fact extent.  Everything else
  is read from what a run already leaves standing — `jtms/dependents` on a rule handle is
  every firing it licensed, and the refusal ledger (`refusals` / `refusal-state`, each
  entry re-decided against *current* belief) is what it completed but did not place — so
  the funnel needs no per-run instrumentation: the stored ledger and the justification
  graph answer it, and a counter beside them would only restate what they already hold.

  Each row is `{:rule :sentence :believed? :placed :refused :refusals :status}`.
  `:placed` is the firing count. `:refused` is `:overflow` when the ledger capped the rule,
  else the entry count. `:refusals` is one map per recorded refusal — its live `:state`
  (`:blocked` / `:dead` / `:free`, re-decided now) and, for one that still blocks, the
  `:reason` (`:post-join` / `:exception` / `:naf` / `:hidden`), plus the `:conseq` it could
  not place and the `:context`. `:status` is `:fires` (placed at least one), `:blocked`
  (placed none, refused at least one), or `:silent` (no antecedent set ever completed —
  nothing placed and nothing refused)."
  [kb]
  (let [rec (:records kb)
        tms (reasoning/tms kb)
        idx (:index kb)
        rule-hs (into (sorted-set) (reads/as-stored-rules-in idx :rule nil))]
    (into []
          (keep (fn [rh]
                  (when-let [rsx (p/get-sentex rec rh)]
                    (when (rules/forward-sentex? rsx)
                      (let [placed  (count (jtms/dependents tms rh))
                            ref     (refusals kb rh)
                            over?   (= :overflow ref)
                            rview   (delay (rule-view-of kb rh rsx))
                            entries (when (set? ref)
                                      (mapv (fn [e]
                                              (let [st (refusal-state kb rh e)]
                                                {:state   st
                                                 :reason  (when (= :blocked st)
                                                            (if (:constraint e)
                                                              :constraint
                                                              (refusal-reason
                                                               kb @rview (:antes e)
                                                               (when (:bindings e)
                                                                 (settled-bindings kb (:bindings e) (:pctx e)))
                                                               (:pctx e))))
                                                 :conseq  (:conseq e)
                                                 :context (:pctx e)}))
                                            ref))
                            exc?    (some #(= :exception (:reason %)) entries)]
                        {:rule      rh
                         :sentence  (sx/authored-sentence rsx)
                         :believed? (boolean (jtms/in? tms rh))
                         :placed    placed
                         :refused   (if over? :overflow (count entries))
                         :refusals  entries
                         ;; the exceptWhen queries that block it, so a blocked-by-exception
                         ;; row can name the exception rather than only its category — forced
                         ;; only when a refusal actually rested on one (`@rview` is already
                         ;; realized by then)
                         :excepts   (when exc? (mapv :query (:excepts @rview)))
                         :status    (cond (pos? placed)              :fires
                                          (or over? (seq entries))   :blocked
                                          :else                      :silent)}))))
                rule-hs))))

(defn release-refusal!
  "Re-derive the refused firing `entry` of rule `rh` and retire the entry, or retire it
  without deriving anything when its support has left.  Returns the handles the
  re-derivation created, for the caller to put back on the agenda.

  **`place-conclusion` with the recorded bindings, never a fresh join** — that is the
  whole cost argument: re-deriving k recorded refusals is k placements, where seeding
  `chain` with the rule handle joins it over the whole fact extent.  The conclusion, its
  placement context and its antecedent list are the ones the refused firing computed, so
  the justification is the one that firing would have made; the depth is recomputed from
  the antecedent facts, as a fresh firing would compute it.

  Re-decided here rather than trusted from the caller's scan: the sweep runs in between,
  and a refusal whose support it collected must not be placed on the strength of an
  answer taken before it ran."
  [kb rh entry]
  (case (refusal-state kb rh entry)
    :blocked []
    :dead    (do (drop-refusal! kb rh entry) [])
    :free    (let [rule  (rule-view kb rh)
                   depth (inc (reduce max 0 (map #(jtms/depth (reasoning/tms kb) %) (:handles entry))))
                   ;; the bound the refusing run was configured with, kept on the entry;
                   ;; the default is the fallback for an entry that carries none — one a
                   ;; rebuild re-recorded before this field existed, or a `:constraint`
                   ;; drop, which `place-fact-conclusion` records without a run config
                   bound (or (:max-depth entry) (:max-depth default-chain-opts))]
               (drop-refusal! kb rh entry)
               (if (> depth bound)
                 []
                 (let [placed (vec (place-conclusion kb rule (:conseq entry) (:pctx entry)
                                                     (:antes entry) depth (:bindings entry)
                                                     (:strength rule) (:subsumptions entry)))]
                   ;; the drop's ledger entry described a conclusion that is now stored,
                   ;; and left standing it would report the arrival order: an order that
                   ;; brought the type first files nothing
                   (when (and (:constraint entry)
                              (kb/find-sentex-handle kb (:conseq entry) (:pctx entry)))
                     (violations/withdraw! kb (:conseq entry) (:pctx entry) rh))
                   placed)))))

;; ---- a permuting mark leaving ---------------------------------------------
;;
;; A mark that stops holding — its last statement retracted, or defeated — leaves rows
;; spelled by it: `(bRel Zed Amy)` asserted under `(symmetric bRel)` is stored as
;; `(bRel Amy Zed)`, and a KB that never held the mark holds the spelling that was
;; written.  Each row keeps the spellings its pieces were written in
;; (`integrate/spellings-key`), and this puts every piece back at the row its spelling
;; canonicalizes to now: a premise assertion re-asserted there at its own class, a rule
;; firing re-placed there with its own antecedents and bindings.  What leaves the old row
;; leaves through the network — the firing dropped, the premise class lowered or taken
;; off — so a row no piece stays on is swept with whatever was drawn from it, which is
;; right: those conclusions read a spelling nobody wrote.  A mark that starts holding
;; again by a relabel has no declaration arriving to fold what it covers, so the same
;; call folds it (`integrate/commute-predicate`).

(defn- reassert-premise
  "Assert `written` in `ctx` at `strength`, unchained and unsettled — the settle this runs
  inside settles it — and return its handle, or nil when the entry point refuses it.  A
  row new here takes `prov`, the provenance of the row the assertion was folded into, so
  it keeps the creation the caller's assertion was stamped with."
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
                 (some #(integer? (:informant (jtms/justification tms %))) (jtms/supports tms h))))))

(defn- sync-respellings!
  "Bring the `respell` justifications resting on row `h` to `want`, `{spelling
  [store alts]}`: each spelling is stored by `store`, a fn answering `[handle sentex
  new?]`, and justified `respell` by `[h & alt]` once for each `alt` of `alts`; a
  `respell` justification resting on `h` whose spelling `want` does not name is dropped.
  Returns the rows it created, for the agenda."
  [kb h want]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        stale (into [] (filter (fn [jid]
                                 (let [j (jtms/justification tms jid)]
                                   (and (= respell-informant (:informant j))
                                        (not (contains? want (:sentence (p/get-sentex recs (:consequence j)))))))))
                    (jtms/dependents tms h))]
    (doseq [jid stale]
      (let [r (jtms/drop-justification! tms jid)]
        (p/delete-justification! recs jid)
        (apply-removals! kb r)))
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
          (sort-by (comp nm/print-key key) want))))

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
                      [s2 [#(integrate/spelled pred ctx e (fn [] (kb/find-or-create-sentex kb s2 ctx)))
                           (or (inherit/permuted-read-supports kb (inner s) (vec (rest (inner s2))) ctx)
                               [[(integrate/mark-witness kb pred)]])]]))
               (when (and (= home s) (piece-holder? kb h)) r)))))))

(defn- split-row!
  "Put each piece of row `sx` whose spelling's home is not the row's own spelling at the
  row it is home at (`integrate/spelling-plan`), store the spellings the readers of each
  moved piece read beside it (`ensure-respellings!`), and only then take the piece off
  this row.  Returns the handles the moves created or re-premised, for the agenda."
  [kb planner sx]
  (let [tms      (reasoning/tms kb)
        recs     (:records kb)
        h        (:id sx)
        stored   (:sentence sx)
        ctx      (:context sx)
        pred     (res/permuted-functor stored)
        plan     (memoize #(integrate/spelling-plan kb planner % ctx))
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
                                                  kb (rule-view kb rh) % ctx (conj (vec (:antecedents j)) rh)
                                                  (inc (reduce max 0 (map (fn [a] (jtms/depth tms a)) (:antecedents j))))
                                                  (:bindings j) (:strength j) (:subsumptions j)))))))
                       (sort-by (comp nm/print-key val) move-d))
        homes    (into (set (vals moved-p))
                       (keep #(at-home % (fn [hw] (kb/find-sentex-handle kb hw ctx))))
                       (vals move-d))
        twins    (into [] (mapcat #(ensure-respellings! kb planner %)) (sort homes))]
    ;; ...and only then off this row, so nothing drawn from the proposition is swept
    ;; while its new row is still being written
    (doseq [jid (keys move-d)]
      (let [r (jtms/drop-justification! tms jid)]
        (p/delete-justification! recs jid)
        (apply-removals! kb r)))
    (when (seq moved-p)
      (if (seq keep-p)
        (let [st (reduce strength/max nil (vals keep-p))]
          (jtms/add-premise tms h st)
          (p/mark-premise recs h st))
        (do (p/unmark-premise! recs h)
            (apply-removals! kb (jtms/retract! tms h)))))
    (when (p/get-sentex recs h)
      (integrate/put-spellings!
       kb h (integrate/normalized-spellings stored {:premise keep-p
                                                    :derived (apply dissoc derived (keys move-d))})))
    (-> (vec (vals moved-p)) (into placed) (into twins))))

(defn- respell-rows!
  "Bring the stored rows `hs` to the spellings their readers read: split each
  (`split-row!`), fold each into the row its spelling is home at
  (`integrate/commute-predicate`'s walk, once per row), then store the spellings each
  row's readers read beside it (`ensure-respellings!`).  Returns the handles that are new
  content, for the agenda."
  [kb hs]
  (let [recs    (:records kb)
        planner (res/spelling-planner kb)
        split   (into [] (mapcat #(some->> (p/get-sentex recs %) (split-row! kb planner))) hs)
        folded  (into [] (keep (fn [h]
                                 (when-let [sx (p/get-sentex recs h)]
                                   (let [pred (res/permuted-functor (:sentence sx))]
                                     (when-let [w (and pred (integrate/permuting? kb pred)
                                                       (integrate/mark-witness kb pred))]
                                       (integrate/fold-row-home! kb planner sx w))))))
                      hs)
        rows    (into (sorted-set) (filter #(p/get-sentex recs %)) (concat hs split folded))]
    (-> split (into folded) (into (mapcat #(ensure-respellings! kb planner %)) rows))))

(defn reconcile-spellings!
  "Bring the stored rows of every predicate in `preds` — the ones whose permuting marks
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
                     (when (pos? (reads/stored-count-with-functor idx pred))
                       (respell-rows! kb (vec (reads/as-stored-with-functor idx pred))))))
           (sort-by nm/print-key preds)))))

(defn- respelling
  "The spelling the write path gives stored row `sx` now (`nat/respelled`), canonical in
  its context, or nil when that is its spelling already.  A mint the respelling owes and
  the entry point refuses leaves the row as it is, logged, as a refused premise spelling
  is (`reassert-premise`)."
  [kb sx]
  (try
    (let [s    (sx/sentence-of sx)
          want (kb/canonical-sentence kb (nat/respelled kb s) (:context sx))]
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
  applications `s` holds, written or as a constant minted for one, sorted."
  [kb s]
  (let [tax (reasoning/taxonomy kb)]
    (->> (tree-seq sequential? seq (nat/expand-expression kb s nat/reified-object-symbol?))
         (keep #(when (and (sequential? %) (seq %)) (first %)))
         (filter #(and (symbol? %) (tax/has-prop? tax :reifiable %)))
         distinct
         (filter #(nat/split-reifiable? kb %))
         sort
         vec)))

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
      (let [ents  (into {} (map #(first (nat/reifiable-entries kb %))) fs)
            rdrs  (or (get @memo [fs ctx])
                      (let [v (into [] (comp (map #(res/entries-at kb ents %)) (distinct))
                                    (res/spelling-readers kb ctx (into [] (mapcat (comp keys val)) ents)))]
                        (vswap! memo assoc [fs ctx] v)
                        v))
            spell (fn [w] (binding [nat/*withheld* w]
                            (kb/canonical-sentence kb (nat/respelled kb s) ctx)))
            sp    (into {} (map (fn [b] (let [w (reduce disj (set fs) (map #(nth % 2) b))]
                                          [(spell w) w])))
                        rdrs)]
        (if (= 1 (count sp))
          (let [[s1 w] (first sp)] [s1 w {}])
          (let [u (spell (set fs))] [u (set fs) (dissoc sp u)]))))))

(defn reconcile-reified!
  "Bring the stored rows a `reifiable_function` mark moving re-spells to the spellings
  their readers read, for every function in `fns` — the ones whose mark moved since the
  last settle (`special/note-permuting-moves!`), or whose readers came to disagree
  (`nat/queue-split-uses!`, `special/note-mark-reach!`) — and return the handles that are
  new content, for the agenda.

  The mark arriving reifies each stored application of `f`, minting what has no term; the
  mark leaving spells each use of a constant minted for `f` with the expression again
  (`nat/respell-region`, `nat/respelled`).  A row moves in place, or folds into the row
  already holding its new spelling (`integrate/move-row!`), carrying its written spellings
  through the same re-spell.  Where the readers of a row disagree on a mark, the row
  stays as written and each other spelling a reader reads is stored justified `respell`
  by it and the mark (`reified-plan`, `sync-respellings!`).  The constants the moved rows
  stop naming are then collected (`collect-respelled-orphans!`).  Linear in the region:
  a declaration written before its applications reaches none of them, and a KB declaring
  no reifiable function never queues one."
  [kb fns]
  (let [recs    (:records kb)
        tax     (reasoning/taxonomy kb)
        tms     (reasoning/tms kb)
        moved   (volatile! [])
        memo    (volatile! {})
        new     (binding [wiring/*defer-settle?* true]
                  (into []
                        (mapcat
                         (fn [f]
                           (let [witness (integrate/witness-among kb (tax/prop-supporters tax :reifiable f))]
                             (into []
                                   (mapcat
                                    (fn [h]
                                      (when-let [sx (p/get-sentex recs h)]
                                        (when (piece-holder? kb h)
                                          (let [s           (sx/sentence-of sx)
                                                ctx         (:context sx)
                                                [home w r]  (reified-plan kb memo s ctx)
                                                h'          (when (not= home s)
                                                              (vswap! moved conj sx)
                                                              (binding [nat/*withheld* (or w #{})]
                                                                (integrate/move-row!
                                                                 kb sx home witness
                                                                 #(binding [nat/*withheld* (or w #{})]
                                                                    (nat/respelled kb %)))))
                                                at          (or h' h)]
                                            (cond-> (sync-respellings!
                                                     kb at
                                                     (into {}
                                                           (map (fn [[s2 w2]]
                                                                  [s2 [#(binding [nat/*withheld* w2]
                                                                          (kb/find-or-create-sentex kb s2 ctx))
                                                                       (into [] (comp (filter (fn [m] (jtms/in? tms m)))
                                                                                      (map vector))
                                                                             (sort (mapcat (fn [g] (tax/prop-supporters tax :reifiable g))
                                                                                           (remove w2 (reified-fns kb s)))))]]))
                                                           r))
                                              h' (conj h')))))))
                                   (map :id (nm/sort-by-content-key #(vector (sx/sentence-of %) (:context %))
                                                                    (nat/respell-region kb f)))))))
                        (sort fns)))]
    (collect-respelled-orphans! kb @moved)
    new))

(defn- fire-rule
  "Apply a newly added rule over existing facts, at the rule's own strength.  `admit` is
  the arrival filter on the facts the join yields (`rule-arrival-admit`), nil for the
  full join a re-join runs."
  ([kb rule-handle max-depth truncated] (fire-rule kb rule-handle max-depth truncated nil))
  ([kb rule-handle max-depth truncated admit]
   (let [{:keys [antecedents consequent] :as rule} (rule-view kb rule-handle)]
     (reduce (fn [nh state]
               (into nh (:new (derive-conclusion kb rule state max-depth truncated))))
             []
             (planned-join kb (vec antecedents) {} (nm/functor consequent)
                           [{:bindings {} :handles [] :matched []}] admit)))))

(defn- delta-fire-rule
  "Re-join one rule over a qualitative **delta**: the same full join `fire-rule` runs, but
  with one qualitative antecedent's enumeration narrowed to the pairs that moved
  (`*qualitative-delta*`), once per such antecedent.  Only the antecedents `calc` answers
  are narrowed: `moved` measures that calculus's networks, and a rule carrying an
  antecedent of a second calculus is re-joined over that one's delta by its own call.

  Falls back to the plain full join when the rule has no qualitative antecedent to narrow,
  or when nothing moved in any context that a delta could be taken for — a cold read, a
  retraction, a network gone unsatisfiable.  That is the same boundary the warm-started
  pass has, and for the same reason: what a widening invalidated is not computable from
  the answer it invalidated."
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
  "Re-join every forward rule mentioning `calc` because a fact of that calculus just
  arrived, and record what they were joined over.

  The re-join is in full rather than at a trigger position because the arriving fact need
  not unify with the antecedent it enabled: a new `nonTangentialProperPart` fact licenses
  a `partOfRegion` antecedent, and the trigger index will never connect the two.  What it
  *is* narrowed by is the delta — the pairs whose entailment has moved since the last time
  these same rules were joined.  A pair that has not moved licenses exactly the firings it
  licensed then, and those were derived then.

  The baseline is recorded whether or not any rule fired, and whether or not any pair
  moved, because \"joined over\" is a claim about this network and not about the outcome.
  It is recorded **after** the join, from the value read before it: the join places
  conclusions as it goes, and a conclusion of this calculus is a datum in its own right
  that will take the next delta against exactly this baseline."
  [kb calc rules max-depth truncated]
  (let [deltas (into {} (map (fn [c] [c (qkb/join-delta kb calc c)]))
                     (calculus-contexts kb calc))
        moved  (update-vals deltas :moved)
        fired  (reduce (fn [nh rh]
                         (let [rsx (p/get-sentex (:records kb) rh)]
                           ;; forward-capable *and believed*: the antecedent index posts
                           ;; on storage, so a defeated or un-believed rule (a defeated
                           ;; mint, a rule concluded by a retracted rule) is still a
                           ;; candidate here, and firing it lands the firing's
                           ;; unconditional side effects — a `:no-placement`/`:disjoint`
                           ;; report against a rule the KB does not believe, `:monotonic`
                           ;; skolem bookkeeping — for a conclusion that only labels OUT.
                           ;; The trigger path refuses it on the record (`fire-rules-for`'s
                           ;; `forward?`); the qualitative re-join must too.
                           (if (and rsx (rules/forward-sentex? rsx) (res/rule-believed? kb rh))
                             (into nh (delta-fire-rule kb calc rh rsx moved max-depth truncated))
                             nh)))
                       []
                       rules)]
    (doseq [[c d] deltas] (qkb/note-joined kb calc c (:baseline d)))
    fired))

(defn- permuting-rejoin-rules
  "The forward rules to re-join because `fact` is a **permuting mark** —
  `(symmetric P)`, `(commutative P)`, `(commutativeInArgs P …)` or
  `(commutativeInArgAndRest P n)` (`inherit/permuting-marks`).

  The matcher reads a literal in another argument order only once its predicate carries
  the mark, so the tuples a `(sibOf ?a ?b)` antecedent reaches change the moment the mark
  lands — and the facts that would have triggered those firings have already arrived, so
  nothing else will enumerate them.  Without this, the same four sentences derive a
  conclusion or not depending on whether the mark came last: 6 of the 24 orderings for
  `symmetric`, and the whole of the difference is that a stored fact means its
  permutations too.  A commutativity mark re-spells a stored fact whose arguments are out
  of order (`integrate/commute-existing`), and that re-spelled row reaches the rules as new
  content; a fact already in canonical order is not re-spelled, and only this re-join
  reaches the orders it now also means.

  `genls(P)`, not `specs`: the matcher asks whether *any sub-predicate* of an
  antecedent's functor carries a mark, so marking `sibOf` moves an antecedent on
  `relatedTo` above it as well as one on `sibOf` itself.  Answered by a symbol compare
  for every datum that is not one of these marks."
  [kb fact]
  (when (and (sequential? fact) (next fact) (inherit/permuting-mark? (nm/functor fact)))
    (let [p (first (nm/args fact))]
      (when (and (symbol? p) (not (sx/variable? p)))
        (not-empty
         (into #{} (mapcat #(reads/as-stored-rules-by-antecedent (:index kb) %))
               (tax/genls-global (reasoning/taxonomy kb) p)))))))

(defn- computed-rejoin-rules
  "The forward rules to re-join because `bfn` is a predicate a registered
  `SupportingProver` **reads** (`provers/support-source-preds`) — the rules carrying an
  antecedent that such a prover answers.

  The qualitative shape one layer over, and needed for the same reason: a
  `(conversionFactor Gram Kilogram 0.001)` decides whether `(quantityGreaterThan ?q
  (QuantityFn 1 Kilogram))` holds of a mass in grams, and nothing connects the two
  predicates — the trigger index keys on the antecedent's own functor, and the facts that
  would have triggered the rule have already arrived.  Without this the same three
  sentences derive a conclusion or not depending on whether the unit table came last.

  `bfn` is the functor of the sentence's **underlying body**, so a believed `(not
  (conversionFactor …))` reaches here too: it defeats the positive row and so moves the
  reading exactly as removing it would.

  Two set lookups for every datum that is not one of these.  For one that is, the stored
  rules' antecedent keys are read once, and the rules only for the answers some rule
  takes.  A supporter reads a `genl` path up to the goal's predicate, so an edge `s`
  installs (`tax/installed-edges`) moves only the answers at or above the edge's upper
  end, read globally because the re-join reads every context."
  [kb bfn s]
  (let [srcs (provers/support-source-preds kb)]
    (when (contains? srcs bfn)
      (let [answers (provers/support-answered-preds kb)
            answers (if (contains? tax/edge-installing-functors bfn)
                      (let [tx    (reasoning/taxonomy kb)
                            above (into #{} (mapcat (fn [[_ super]] (tax/genls-global tx super)))
                                        (tax/installed-edges s))]
                        (filter above answers))
                      answers)]
        (when (seq answers)
          (let [idx   (:index kb)
                ruled (reads/as-stored-rule-keys idx)]
            (not-empty
             (into #{} (comp (filter #(contains? ruled %))
                             (mapcat #(reads/as-stored-rules-by-antecedent idx %)))
                   answers))))))))

(defn- transitive-rejoin-rules
  "The forward rules to re-join because the arriving datum moved a transitive walk — it is
  the `(transitive P)` **declaration** that turns one on, or an **edge** of one already
  declared: a fact on that predicate, on a sub-predicate of it, or on a partner an
  `inverse` records its hops on.

  The declaration half is the `(symmetric P)` case exactly (`permuting-rejoin-rules`): it
  changes which pairs a `P` antecedent reaches, and the facts it reaches them over have
  already arrived, so nothing about `P` would ever bring the rule round again.  The
  antecedent's **own** functor has to be the declared one for the join to walk
  (`transitive-antecedent?`), so this keys on `P` itself rather than on its `genl`
  closure.

  The same problem `computed-rejoin-rules` solves one predicate family over, and the same
  answer.  An arriving `(causes B C)` triggers a `(causes ?a ?c)` antecedent at the tuple
  it is *stated* at, `?a = B`; the pair it licenses through an already-stored `(causes A
  B)` is `?a = A`, and no trigger enumerates that.  Without the re-join the same three
  sentences derive a conclusion or not depending on which hop of the chain arrived last.

  `bfn` is the functor of the sentence's **underlying body**, so a believed `(not (causes
  B C))` reaches here too: it defeats the edge and so breaks the chain exactly as removing
  it would.

  Over-approximating on purpose: a rule whose own conclusion is what it would walk takes
  the matcher's answers alone (`walks-its-own-conclusion?`), and re-joining it in full
  derives exactly what triggering it would.  A re-join too many is a firing the TMS dedups;
  one too few is a conclusion that depends on which hop arrived last.

  A symbol compare and one map read for every datum that is neither.  On a KB that does
  declare a transitive predicate the edge half is a memoized `genls` closure read and a
  handful of set lookups — and its `inverse` arm adds no work at all until some KB
  declares an inverse, `inverses-under` answering empty off one map read until then."
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
       (into #{} (mapcat #(reads/as-stored-rules-by-antecedent (:index kb) %)) hit)))))

(defn- closure-rejoin-rules
  "The forward rules to re-join because the arriving datum is a `genl` or `genlCx` edge —
  the rules carrying an antecedent on the same relation, which the join answers from the
  closure (`solve-closure`).

  An arriving `(genl b c)` triggers a `(genl ?x ?y)` antecedent at the tuple it is
  stated at.  The pairs it adds to the closure through edges already stored, `(genl a
  c)` below `b` and the ones above `c`, are reached by joining, and no trigger enumerates
  them — `transitive-rejoin-rules`' reason, for a cached closure.

  A cover adds `genl` edges without being one (`special/closure-edge-relation`), so it
  re-joins the rules reading `genl`.

  Gated on the stored antecedent keys, so an edge on a KB with no rule reading the
  relation costs a symbol compare and one membership test."
  [kb fact]
  (when-let [f (special/closure-edge-relation fact)]
    (when (reads/stored-rule-key? (:index kb) f)
      (not-empty (into #{} (reads/as-stored-rules-by-antecedent (:index kb) f))))))

(defn- rejoin-in-full
  "Re-join in full every forward rule the arriving datum moved a preserved predicate
  for, newly declared symmetric, fed a `SupportingProver` a source it reads, gave a
  new hop to a transitive predicate's walk, or gave a new edge to the `genl` / `genlCx`
  closure a closure antecedent reads.

  In full rather than at a trigger position, and the reason is the qualitative one: the
  arriving sentence need not unify with the antecedent it enabled.  `(genl chihuahua
  dog)` licenses a `largerThan` antecedent, and no walk from `genl` reaches
  `largerThan` — the predicate-keyed trigger index cannot connect the two.  Nor is a
  claim on the predicate itself enough on its own: `(largerThan dog cat)` unifies with
  the antecedent at the one tuple it is *stated* at, and the tuples it licenses are
  reached by joining rather than by matching.

  Bounded by the rules carrying an antecedent on a declared predicate, which is none
  for every KB that declares no preservation and none for nearly every KB that does.
  The symmetric caller is bounded the same way — by the rules with an antecedent over
  the predicate just declared — and is reached only by a declaration datum.  So is the
  computed one: by the rules with a `support-answered-preds` antecedent, and reached only
  by a datum on a predicate some registered prover reads.  So is the transitive one: by the
  rules with an antecedent on a declared-transitive predicate, and reached only by a datum
  on an edge of one.  So is the closure one: by the rules with a `genl` / `genlCx`
  antecedent, and reached only by an edge of that relation."
  [kb rules max-depth truncated]
  (reduce (fn [nh rh]
            (let [rsx (p/get-sentex (:records kb) rh)]
              ;; forward-capable *and believed*, for the reason `rejoin-qualitative` and
              ;; `fire-rules-for`'s `forward?` state: the index posts on storage, so an
              ;; un-believed rule reaches here and its firing's side effects land though
              ;; the conclusion only labels OUT.
              (if (and rsx (rules/forward-sentex? rsx) (res/rule-believed? kb rh))
                (into nh (fire-rule kb rh max-depth truncated))
                nh)))
          []
          rules))

(defn triggers-rules?
  "Can the ground `fact`, arriving, fire or re-join a forward rule: one keyed by its
  predicate or a supertype (`rules/trigger-keys`), a calculus it moves, a preserved,
  permuting, computed, transitive or closure re-join (`fire-rules-for`'s sources)?
  Storage, not belief: a rule the index posts counts whether or not it is believed."
  [kb fact]
  (let [ffn  (nm/functor fact)
        body (if (= sx/not-functor ffn) (kb/body-under-not fact) fact)
        bfn  (nm/functor body)]
    (boolean
     (or (seq (rules/trigger-keys (reasoning/taxonomy kb) fact (reads/as-stored-rule-keys (:index kb))))
         (seq (qkb/calculi-triggered-by kb bfn))
         (inherit/rejoin-rules kb fact)
         (permuting-rejoin-rules kb fact)
         (computed-rejoin-rules kb bfn body)
         (transitive-rejoin-rules kb fact bfn)
         (closure-rejoin-rules kb fact)))))

(defn- stale-closure-rejoins
  "The rules of `rules` that this run has not re-joined in full at the current
  `special/taxonomy-generations` stamp, recording each forward, believed one at that stamp
  in `*closure-rejoins*`.  Outside a run, `rules` unchanged."
  [kb rules]
  (if-let [^java.util.HashMap seen (when rules *closure-rejoins*)]
    (let [stamp (special/taxonomy-generations kb)]
      (not-empty
       (into #{}
             (filter (fn [rh]
                       (when (not= stamp (.get seen rh))
                         (let [rsx (p/get-sentex (:records kb) rh)]
                           (when (and rsx (rules/forward-sentex? rsx) (res/rule-believed? kb rh))
                             (.put seen rh stamp)))
                         true)))
             rules)))
    rules))

(defn- fire-rules-for
  "Fire every forward rule a newly asserted fact can trigger — **strict and
  defeasible alike**.  Candidate rules are keyed by the fact's predicate and its
  supertypes (specificity), and each fires at its own strength
  (`provers/firing-strength`).

  A default conclusion is placed **unconditionally**, with defeat decided afterwards
  by `settle` from the recomputed belief state, so firing order affects only how
  expensively a datum is found, never *what* is derived: the result is the least
  fixpoint of a monotone immediate-consequence operator regardless of order.  A bare
  consequence of a default conclusion still arrives, because that conclusion lands on
  the agenda and triggers bare rules like any other new datum.  The depth guard
  applies equally — a default conclusion carries `1 + max` antecedent depth through
  `derive-conclusion`, so a default rule cannot outrun `:max-depth` any more than a
  bare one can, and its truncation reaches the run's `:truncated?` flag."
  [kb datum max-depth truncated]
  (let [fact     (:sentence (p/get-sentex (:records kb) datum))
        ffn      (nm/functor fact)
        ;; read once per datum, not per candidate position: what makes the mirror true is
        ;; the fact's own `symmetric` declaration, and every position asks the same fact
        mirror   (symmetric-mirror kb fact)
        ;; and, at any arity, the components the fact's own predicate licences — read
        ;; once per datum for the same reason the mirror is
        comps    (commuting-components-of kb fact)
        ;; a positive fact's predicate and its supertypes; a negative fact's `[:not q]`
        ;; keys for the specs `q` of its body's predicate, which is the direction a genl
        ;; edge carries through a negation — read off the rule roster rather than off
        ;; that closure (`rules/trigger-keys`)
        preds    (rules/trigger-keys (reasoning/taxonomy kb) fact (reads/as-stored-rule-keys (:index kb)))
        ;; the antecedent index is complete and posts on storage, so each candidate's own
        ;; record decides whether it may fire here — forward-capable, and believed, which
        ;; for a rule is `res/rule-believed?` rather than the `jtms/in?` a fact takes
        ;; (a rule the TMS holds no node for is available, not disbelieved)
        rhs      (into #{} (mapcat #(reads/as-stored-rules-by-antecedent (:index kb) %)) preds)
        ;; A qualitative fact changes the *whole* network, so it can license an
        ;; entailment on any predicate of its calculus — including predicates the
        ;; trigger index would never connect it to, since a new `ntpp` fact licenses a
        ;; `partOfRegion` antecedent and the two are unrelated by genl.  Those rules go
        ;; to `rejoin-qualitative`, which re-joins them over the pairs that moved rather
        ;; than at a trigger position.  A *negative* fact reaches its calculus by the
        ;; predicate under the `not`: its own functor names nothing, and it narrows the
        ;; network by the complement of the denotation exactly as a positive one narrows
        ;; it by the denotation, so it too can entail a relation nobody stated — and the
        ;; arriving fact is the only thing that queues the re-join that finds one.
        ;;
        ;; Which is a symbol comparison, not a peel: the functor is in hand either way,
        ;; and only a `not` pays `body-under-not` (structural, on a record's already
        ;; canonical sentence — `sx/underlying-body` would rebuild and re-intern the
        ;; whole sentence to answer the same question).  This runs per datum for every
        ;; fact a chaining run touches, qualitative or not and prover or none.
        ;;
        ;; `calculi-triggered-by`, because a network has readers besides its own stored
        ;; facts: the interval algebra takes a metric **narrowing** from `stp`, so a
        ;; `temporalDistance` or a `startOf` moves what is entailed between two intervals
        ;; while being a predicate no interval rule mentions.  The rules re-joined are
        ;; still the ones carrying an antecedent the calculus *answers*, per calculus the
        ;; datum moves — an instant fact moves the point network and the Allen one.  A
        ;; `(genl sub super)` edge moves what a `super` fact does, since the network
        ;; reads `sub`'s facts through the matcher's fan.
        bfn      (if (= sx/not-functor ffn) (nm/functor (kb/body-under-not fact)) ffn)
        qrules   (when-let [cs (qkb/calculi-triggered-by
                                kb (if (and (= 'genl ffn) (= 3 (count fact))) (nth fact 2) bfn))]
                   (mapv (fn [c]
                           [c (into #{} (mapcat #(reads/as-stored-rules-by-antecedent (:index kb) %))
                                    (:predicates c))])
                         cs))
        qrhs     (when qrules (not-empty (into #{} (mapcat second) qrules)))
        ;; The same shape one layer over, and the same reason: a sentence can move what
        ;; a preserved predicate licenses without being on that predicate — a `genl`
        ;; edge, a fact on the relation, the declaration, `(transitive R)` — and a
        ;; claim that *is* on it reaches the antecedent only at the tuple it is stated
        ;; at.  `inherit/rejoin-rules` reads the declarations to say which rules those
        ;; are, and answers nil off two predicate-extent counts for a KB that declares
        ;; none.
        prhs     (inherit/rejoin-rules kb fact)
        ;; And one layer over again, for the matcher rather than for a prover: a
        ;; `(symmetric P)` or commutativity datum changes which tuples a P antecedent
        ;; reaches, and the facts it reaches them over have already arrived.  A symbol
        ;; compare for every datum that is not such a mark.
        srhs     (permuting-rejoin-rules kb fact)
        ;; And once more for a prover rather than for the matcher: a datum on a predicate
        ;; a `SupportingProver` reads moves what a computed antecedent answers, and no
        ;; walk from `conversionFactor` reaches `quantityGreaterThan`.
        crhs     (computed-rejoin-rules
                  kb bfn (if (= sx/not-functor ffn) (kb/body-under-not fact) fact))
        ;; And once more for the walk rather than for the table: an arriving edge makes
        ;; pairs a `(transitive P)` antecedent reaches through it, and the trigger index
        ;; offers only the tuple the edge is stated at.
        trhs     (transitive-rejoin-rules kb fact bfn)
        ;; ...and for a cached closure: an arriving `genl` / `genlCx` edge adds pairs a
        ;; closure antecedent reaches through the edges already stored
        grhs     (stale-closure-rejoins kb (closure-rejoin-rules kb fact))
        trigger  (cond->> rhs
                   qrhs (remove qrhs)
                   prhs (remove prhs)
                   srhs (remove srhs)
                   crhs (remove crhs)
                   trhs (remove trhs)
                   grhs (remove grhs))
        ;; forward-capable *and believed*: the antecedent index posts on storage, so a
        ;; rule whose support has gone is still a candidate here and is refused on its
        ;; record rather than by the lookup (`res/rule-believed?`)
        forward? (fn [rh rsx] (and rsx (rules/forward-sentex? rsx)
                                   (res/rule-believed? kb rh)))
        ;; A rule that reached this run's agenda **after** the datum enumerates the
        ;; datum's firings from its own full join, which admits every fact that arrived
        ;; before it (`rule-arrival-admit`), so the datum leaves them to it.  Only where
        ;; that join is sure to find the datum: a **believed** one, since the join is
        ;; belief-filtered, and one whose match no mark of its own rearranges, since the
        ;; trigger follows the fact's mirror and components (`read-marks`) where the
        ;; join is not asked to.
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
        (let [rsx (p/get-sentex (:records kb) rh)]
          (if (or (not (forward? rh rsx)) (and later-rule? (later-rule? rh)))
            nh
            ;; The trigger match runs over the record's own antecedents, and the
            ;; chainer's view — which re-derives them beside the NAF and post-join
            ;; literals and probes the exception roster — is built only once a
            ;; position unifies.  A candidate is any rule with an antecedent on the
            ;; datum's predicate or a supertype of it, and for a broad type most of
            ;; them unify at none of their positions; the view is a per-firing cost,
            ;; not a per-candidate one.
            (let [antecedents (:antecedent rsx)
                  cpred       (nm/functor (:consequent rsx))
                  rule        (delay (rule-view-of kb rh rsx))]
              (reduce (fn [nh2 i]
                        (reduce
                         (fn [nh3 b0]
                           (reduce (fn [nh4 state]
                                     (into nh4 (:new (derive-conclusion kb @rule state max-depth truncated))))
                                   nh3
                                   (complete-antecedents
                                    kb antecedents i datum b0
                                    ;; only the fact's own mark rearranges it at a trigger
                                    (if (or mirror comps)
                                      (read-marks kb (nth antecedents i) b0 datum nil)
                                      [[]])
                                    cpred)))
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
      (when (seq crhs) (rejoin-in-full kb crhs max-depth truncated))
      (when (seq trhs) (rejoin-in-full kb trhs max-depth truncated))
      (when (seq grhs) (rejoin-in-full kb grhs max-depth truncated))))))

(defn- process-datum
  "In a global chain, a rule datum fires if it is forward-capable — defeasible or
  not (a backward/inert rule never forward-chains).  A fact fires the rules keyed
  by it.

  `*qcn-contexts*` is bound **per datum**, and the scope is the point.  Which contexts a
  calculus has facts in is a function of the store, and a run changes the store — so
  caching it across the whole run would let a rule that concludes a qualitative relation
  go on reading the contexts as they were before.  Per datum is safe *because* a placed
  qualitative conclusion becomes a datum in its own right, and processing that datum
  re-joins every rule mentioning its calculus (`fire-rules-for`).  So a context enabled
  mid-datum is not lost, only deferred by one agenda step — which is what the fixpoint is
  for.

  The networks are resident on the KB and stamped with the change clock, so they need no
  cache of their own here — but they do need `observe/with-pin`, and for a reason the
  clock cannot supply.  A join is a lazy seq whose solutions are *placed* as they are
  taken, so the datum writes while it reads; pinning is what makes the whole step join
  against one network rather than against a network that moves under it."
  [kb datum max-depth truncated]
  (observe/with-pin
    (binding [*qcn-contexts* (atom {})]
      (let [sx (p/get-sentex (:records kb) datum)]
        (if (rules/rule? sx)
          ;; direction and defeasibility are read straight off the record — the sentex
          ;; is already in hand, and it is what the set/*Rule wrapper set.  A defeasible
          ;; rule fires here too, at :default (see fire-rules-for).  Belief is asked
          ;; here as well as there: a rule reaches the agenda as a *datum* when it is
          ;; asserted or derived, and a derived one can arrive already defeated.
          (if (and (rules/forward-sentex? sx) (res/rule-believed? kb datum))
            (fire-rule kb datum max-depth truncated (rule-arrival-admit datum))
            [])
          ;; A **superseded** fact is the one unbelieved datum that does not fire, and
          ;; the asymmetry with a defeated one is the whole of the reason.  A defeat is
          ;; a label, so a conclusion drawn off a defeated antecedent is labelled OUT
          ;; with it and revives with it — which is why an OUT datum is enumerated here
          ;; at all (`arrival-admit`).  A supersession is not a label: it is deliberately
          ;; **not** a forced OUT inside the fixpoint, since the twin is justified by
          ;; the spelling it displaced (docs/equality.md), so a conclusion drawn off a
          ;; retired spelling would stay believed under that spelling while every read
          ;; asks after the representative — the same knowledge deriving one conclusion
          ;; where the merge preceded the fact and two where it followed.  The
          ;; restatement is on the agenda beside this datum, so the firing is not lost,
          ;; it is made once at the elected spelling; and when the merge goes away the
          ;; spelling comes back through `settle`'s un-merge channel and fires then
          ;; (docs/nmtms.md).
          (if (jtms/superseded? (reasoning/tms kb) datum)
            []
            (fire-rules-for kb datum max-depth truncated)))))))

(defn chain
  "Semi-naive fixpoint forward chaining seeded with `seed`, strict and defeasible
  rules together on the one agenda.

  `opts` may carry an **`:on-progress`** callback, called about four times a second
  (`:progress-every-ms`) with
  `{:derived n :pending n}` — what the run has concluded, and how much agenda is left.  A
  fixpoint has no total to count towards (the agenda grows as it derives), so those two
  numbers are all a run can report of where it is; both are O(1) to take.  The callback
  may **throw**, which aborts the run — the one interruption point chaining has, and how a
  loader cancels one.  What had already been derived stays: the conclusions are placed as
  they are made, so an aborted fixpoint is a KB holding a prefix of the run, not a corrupt
  one.

  Reporting happens at two points, and it takes both to keep a bar moving: at the agenda
  loop, which sees the run between datums, and at each rule firing (`*tick*`), which is
  inside the one datum that can run for minutes.  The remaining silent stretch is a single
  *unproductive* join — a match search that yields nothing for a long time never reaches a
  firing — which is bounded by the extent it is scanning rather than by the corpus."
  [kb seed opts]
  ;; The generative join is `settle-phases`' `:chaining` centre — a bulk load fires it per
  ;; assert, a `recover` not at all.  Wraps `chain` alone: `chain-all` and the settle
  ;; re-chain both route through here, and the span nests cleanly when they do.
  (phases/with-phase :chaining
    (let [{:keys [max-depth max-derivations on-progress progress-every-ms]}
          (merge default-chain-opts opts)
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
          ;; the agenda's own order, recorded so a firing both sides could make is made
          ;; once (`*agenda-arrivals*`).  A fresh map per run rather than an outer one
          ;; reused, unlike the two caches beside it: these are positions in *this*
          ;; agenda, and a nested run (an `:on-progress` callback may start one) has
          ;; its own.
          arrivals  (when *suppress-duplicate-firings* (java.util.HashMap.))
          arrived   (volatile! 0)
          arrive!   (fn [hs]
                      (when arrivals
                        (doseq [h hs] (.put ^java.util.Map arrivals h (vswap! arrived inc)))))]
      ;; the tick is bound whether or not anybody is listening: it is also how the run
      ;; counts what it derived, and the loop cannot see that between datums.
      ;; The handle cache is engaged for the same scope, and for the reason that scope
      ;; exists: a fixpoint asks "is this conclusion already stored?" once per witness, so
      ;; a conclusion reached k ways is k walks of the trie to a handle this run minted
      ;; itself.  Nothing is removed from the store inside a run — `settle` runs after it —
      ;; so every entry stays true for as long as the cache is bound.
      ;; The justification dedup index rides the same scope for the sibling question —
      ;; "does this conclusion already hold this justification?", also asked once per
      ;; witness — and the same argument covers it: nothing removes a justification
      ;; inside a run, and the two paths that do (`jtms/retract!`, `jtms/sweep!`) clear
      ;; it themselves.  It is scoped to this KB's TMS, so a nested run over another KB
      ;; (an `:on-progress` callback may start one) gets its own index, not this one.
      ;; The arrival ledger is the third thing on that scope, and it is the agenda's own
      ;; order rather than a cache of anything — a datum is stamped as it is enqueued,
      ;; before any datum behind it is processed, so the trigger of a pair is always the
      ;; one the ledger sorts later.
      (observe/with-handle-cache
        (jtms/with-dedup-cache (reasoning/tms kb)
          (binding [*tick* (fn [n]
                             (vswap! placed + n)
                             (when (and on-progress (due?)) (report!)))
                    ;; the fourth thing on this scope, and the sibling of the handle cache
                    ;; above it: a per-functor verdict on whether that cache is authoritative
                    ;; (the store held nothing under the functor when the run began), so a
                    ;; novel conclusion of a chain-only predicate skips the trie walk that
                    ;; would only reconfirm the cache's own miss (`kb/find-sentex-handle`).
                    ;; A fresh map per run, like `arrivals`: it is a claim about *this*
                    ;; run's store, and a nested run gets its own.  Armed only for a bulk
                    ;; frontier (`kb/chain-authority-min-frontier`) — an incremental assert's
                    ;; one-fact seed concludes too little to repay the probe, so it stays nil
                    ;; and `find-sentex-handle` walks the trie, which is the reference path.
                    kb/*chain-authoritative-functors* (when (>= (count seed)
                                                                kb/chain-authority-min-frontier)
                                                        (java.util.HashMap.))
                    ;; The KB's registered evaluatables, read once: the registry is fixed
                    ;; for a run, and forward chaining reads this set on the hot join path to
                    ;; treat an `add-evaluatable` predicate as a computed antecedent
                    ;; (`deferred-antecedent?`).  A nested run over another KB rebinds it to
                    ;; that KB's set.  Empty for the common KB with none.
                    *evaluatable-preds* (provers/evaluatable-preds kb)
                    ;; Whether the KB declares any preservation, read on the first join
                    ;; that asks and forgotten when a firing places a declaration
                    ;; (`note-placed-declaration!`) — per run, and a fresh cell per run
                    ;; for the reason `arrivals` is.
                    *declarations-cell* (volatile! nil)
                    ;; One full closure re-join per rule per closure stamp: a departing
                    ;; `genlCx` edge re-chains every `genl` fact above it, and each one
                    ;; would otherwise re-join the same rules in full.
                    *closure-rejoins* (java.util.HashMap.)
                    *agenda-arrivals* arrivals]
            (arrive! seed)
            (loop [agenda (into clojure.lang.PersistentQueue/EMPTY seed)]
              (if (or (empty? agenda) (>= @placed max-derivations))
                (do (vreset! pending (count agenda))
                    (when on-progress (report!))
                    {:derived @placed :truncated? (or @truncated (>= @placed max-derivations))})
                (let [d       (peek agenda)
                      new-hs  (process-datum kb d max-depth truncated)
                      _       (arrive! new-hs)
                      agenda' (into (pop agenda) new-hs)]
                  (vreset! pending (count agenda'))
                  (when (and on-progress (due?)) (report!))
                  (recur agenda'))))))))))

(defn rerecord-refusals!
  "Rebuild the refusal record by re-firing every rule that can refuse a firing.
  Returns the chain result, or nil for a KB where no rule carries a re-checkable block
  condition.

  `recover`'s half of the record.  A refused firing left no justification, so nothing in
  the store holds it and replaying the stored justifications cannot bring it back — the
  record is derived state and is rebuilt the way blocking is, by re-deciding rather than
  by reading.  Re-firing is what re-decides it: a firing that can be placed is placed and
  deduped by `has-justification?`, and one that is refused re-records.

  Run **after** the settle that establishes belief, since a refusal is a claim about what
  the KB believes, and `relabel` deliberately lands unblocked.  `!` because it discards
  the record it replaces.

  Re-fires at the **default** depth bound — `(chain kb live nil)` carries no run config —
  so the rebuilt entries record that default rather than whatever bound each original run
  set.  A run's `:max-depth` is transient live-session config no store holds, exactly as
  `recover` resets derivation depths to 0 (a bound only governs *future* chaining), so a
  KB chained under a non-default bound rebuilds its refusals, and releases them, at the
  default.  The recovered KB is internally consistent at that default; docs/exceptions.md
  states the one narrow case it can differ from the live session in."
  [kb]
  (when-let [roster (seq (reads/watched-rules (:index kb)))]
    (reset! (reasoning/refused kb) {})
    (let [live (filterv (fn [rh]
                          (let [rsx (p/get-sentex (:records kb) rh)]
                            (and rsx (rules/rule? rsx) (rules/forward-sentex? rsx)
                                 (jtms/in? (reasoning/tms kb) rh))))
                        roster)]
      (when (seq live) (chain kb live nil)))))

(defn chain-all
  "One fixpoint from `seed`, strict and defeasible rules on the same agenda (there
  is no separate defaults phase — see `fire-rules-for`).

  Opens a new run in `chain-stats` — violations recorded during the run carry its
  id — and stashes the result there, warning when the run was truncated.  The ledger
  **accumulates** across runs rather than resetting per run, so a bulk load's drops
  stay observable one assert later; and because internal callers discard the
  `:truncated?` flag, the :warn log is how a depth-capped chain's lost conclusions
  surface.

  At `:debug` every run says what it did, truncated or not — the run is the boundary a
  log statement belongs at, and without one a chain that concluded nothing, a chain that
  concluded forty thousand things and a chain still joining are the same silence to
  somebody watching a load."
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
                   :msg "forward chaining was truncated (max-depth or max-derivations) — conclusions are missing"
                   :data result}))
    result))

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :R11 :label "Chaining run memos" :kind :pass :keyed-by :value :reads [:index :records]
  :retired-by {} :computed :pass :imaged? false :var #'*declarations-cell*
  :note "`*agenda-arrivals*`, `*declarations-cell*`, `*closure-rejoins*`, `*evaluatable-preds*` for one run and `*qcn-contexts*` for one datum"})
