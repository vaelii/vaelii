;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.solve-context
  "Solving as a **persistent, inert** artifact: `assumptionRules` define choices, a
  solve grounds them (scoped to a base context), enumerates the optimal answer sets,
  and materializes **each one as its own labeling context** — a `genlCx` child of
  the base holding the chosen truth values as inert sentexes.  `classify` then gathers
  brave/cautious over those labelings.

  The two imperatives `(do/label Base Into)` and `(do/classify Into)` route here.

  ## Why inert, and why per-answer-set

  Belief in this KB is global (one JTMS, not an ATMS): a *believed* `(not head)` in a
  context that sees the base would defeat the base's `head` everywhere — so only one
  labeling could ever exist (the `do/labeling` global-commit).  Materializing the truth
  values **inert** (`core/assert-inert` — stored and indexed but not a JTMS premise)
  sidesteps that entirely: an inert sentex is never IN, so it is invisible to the
  belief-filtered nogood scan, forms no contradiction, and moves no belief.  Every
  answer set therefore coexists as its own context, the base KB is untouched, and the
  result **persists in the records** for inspection.

  ## What persists, and what does not

  The **answer** persists: the labeling contexts and the classification, as inert
  sentexes in the records.  The **grounding** — the menu of candidate choice heads —
  never does.  A grounding is derived solver working state, recomputable from the
  assumptionRules and the base's believed facts; an inert copy would carry no
  justification linking it back to what produced it, so it would rot silently the
  moment the base moved.  The Program keys on program-local ids (see `build`), and
  `label` returns the menu as `:choices` for a caller who wants to see it.

  And what persists is **replaced on re-run**, never accreted: `label` clears a
  previous run's artifacts under the same `Into` before writing (see `clear-run!`),
  and `classify` clears its own previous classification.  Truth values from two
  different groundings unioned into one context assert nothing at all.

  ## What a choice constrains (docs/solving.md)

  Constraints reach the **direct** ground choice heads and nothing further: the engine's
  own contradictions among them — a `(not X)`/`X` pair, a `functional` predicate given
  two values, a `disjoint` type clash — and every `hardConstraint` / `softConstraint`
  rule ground over them.  Choices do **not** propagate through ordinary rules, because
  the Program is built from the choice heads and the nogoods standing over them: nothing
  runs the chainer with a choice held hypothetically, and nothing emits the rule base to
  a grounder.  A constraint that only bites downstream of a rule has nothing to bite on."
  (:require [clojure.set :as set]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wiring :as wiring]))

;; The below-core read of a context's stored extent — all records, believed or not
;; (the callers filter belief with `jtms/in?` / `res/rule-believed?` themselves).  This
;; is the below-`vaelii.core` form of `vaelii.core/sentexes-in-context` with default opts:
;; `records-of` over the index's stored handles.
(defn- stored-in [kb ctx]
  (keep #(p/get-sentex (:records kb) %) (reads/as-stored-in-context (:index kb) ctx)))

;; ---- context naming and ownership ----------------------------------------
;; `Into` is a context name (`Cx`-prefixed) that seeds the run's artifact names by
;; appending to it directly — the prefix is already there, so nothing is stripped or
;; re-added: labelings are numbered `<Into>1`, `<Into>2`, …, and the classification
;; lands in `<Into>Class`.  The names are for humans;
;; **ownership is recorded, never inferred from a name**: each labeling context
;; carries an inert `(labelingOf <ctx> <Into> <i>)` marker, and rediscovery reads
;; the markers back through the term index.  So a user context that happens to be
;; named `<Into><i>` is neither read by `classify` nor swept by a re-run —
;; a name pattern would make both mistakes, and with a destructive sweep the
;; second one is data loss.

(defn- ctx-sym [base & parts] (symbol (apply str (name base) parts)))
(defn- class-context [into-cx]      (ctx-sym into-cx "Class"))
(defn- labeling-context [into-cx i] (ctx-sym into-cx i))

(defn- marker?
  "Is this stored sentence a `labelingOf` ownership marker?"
  [sentence]
  (and (seq? sentence) (= 'labelingOf (first sentence))))

(defn- labeling-contexts
  "The labeling contexts a prior `label` created for `into-cx`, in labeling order —
  read from the `(labelingOf <ctx> <Into> <i>)` marker each one carries, through
  the term index.  Exact ownership, no name pattern (see the naming comment)."
  [kb into-cx]
  (->> (kb/find-sentexes kb into-cx)
       (keep (fn [s]
               (let [f (:sentence s)]
                 (when (and (marker? f) (= into-cx (nth f 2 nil)))
                   [(nth f 3 0) (second f)]))))
       (sort-by first)
       (mapv second)))

(defn- free-labeling-contexts
  "Labeling context names for `n` answer sets: `<Into><i>` counting up from 1,
  skipping any name an unrelated context already occupies — in the hierarchy, or
  with a non-empty extent.  A re-run's own previous contexts were cleared just
  before this runs, so they do not block their own slots; a user context that
  happens to share the naming is never written into (the marker keeps it out of
  rediscovery, this keeps it out of materialization)."
  [kb into-cx n]
  (let [existing (set (tax/contexts (reasoning/taxonomy kb)))
        taken?   (fn [c] (or (existing c) (pos? (reads/stored-count-in-context (:index kb) c))))]
    (->> (iterate inc 1)
         (map #(labeling-context into-cx %))
         (remove taken?)
         (take n)
         vec)))

;; ---- replace-on-rerun ----------------------------------------------------

(defn- believed-extent?
  "Does `ctx` hold a **believed** sentex?  Everything a solve writes into its own
  contexts is inert by construction, so one that answers true is not a solve artifact —
  or is one somebody has since written into."
  [kb ctx]
  (boolean (some #(jtms/in? (reasoning/tms kb) (:id %)) (stored-in kb ctx))))

(defn- placed-under?
  "Does `ctx` carry the one `(genlCx ctx base)` edge a solve writes to place a labeling
  under `base`?  The signature of this run's own materialization: matched whole rather
  than by functor, exactly as `clear-context!` matches the edge it retracts."
  [kb ctx base]
  (boolean (some #(= (:sentence %) (list 'genlCx ctx base)) (kb/find-sentexes kb ctx))))

(defn- marked-for?
  "Does `ctx` carry a `labelingOf` ownership marker naming `into-cx`?"
  [kb ctx into-cx]
  (boolean (some (fn [{:keys [sentence]}]
                   (and (marker? sentence)
                        (= ctx (second sentence))
                        (= into-cx (nth sentence 2 nil))))
                 (stored-in kb ctx))))

(defn- blocked-artifacts
  "What stands between a re-run and the replace-on-rerun promise, as
  `{:believed [ctx …] :orphaned [ctx …]}` — both empty when nothing does.

  **`:believed`** is a context `clear-context!` would decline to touch.  Declining is
  right — the sweep must never destroy knowledge — but *proceeding afterwards* is not:
  the old marker survives beside the new run's, and `classify` then aggregates two
  groundings into one classification, which is the accretion the ns docstring says must
  never happen.

  **`:orphaned`** is a labeling whose ownership marker is gone.  The marker is an
  ordinary retractable sentex and `labeling-contexts` is the only discovery path, so
  losing one makes the context invisible to the sweep forever while its `genlCx` edge
  goes on holding it in the hierarchy — a believed monotonic edge nothing will ever
  retract, and one more leaked slot per re-run.  It cannot be found by its marker, so it
  is recognized by everything else a marker-less artifact still is: a name in the
  `<Into><i>` series, a **non-empty** extent with nothing believed in it, this run's own
  placement edge under `base`, and no marker.  The series is walked only as far as the
  first free slot, since materialization never skips one.

  All four together, because a name pattern here is used to *ask* and never to sweep —
  the distinction the naming comment draws — and each condition is what keeps a
  context of somebody's own out of the question.  Believed content is the ordinary mark
  of one and is decisive: a user context occupying a slot, even one they hung under this
  very base, holds what they asserted and is neither swept nor refused over.  So the two
  categories are disjoint, and the residue — a marker retracted *and* believed content
  written in — is indistinguishable from the user's context, which is what it has become."
  [kb base into-cx]
  (let [existing (set (tax/contexts (reasoning/taxonomy kb)))
        taken?   (fn [c] (or (existing c) (pos? (reads/stored-count-in-context (:index kb) c))))
        slots    (take-while taken? (map #(labeling-context into-cx %) (iterate inc 1)))
        mine     (set (labeling-contexts kb into-cx))]
    {:believed (filterv #(believed-extent? kb %)
                        (conj (vec mine) (class-context into-cx)))
     :orphaned (filterv #(and (not (mine %))
                              (seq (stored-in kb %))
                              (not (believed-extent? kb %))
                              (placed-under? kb % base)
                              (not (marked-for? kb % into-cx)))
                        slots)}))

(defn- refuse-blocked-run!
  "Refuse the run when `blocked-artifacts` finds anything.  A solve replaces what the
  previous one under this `Into` left, and a run that cannot do that must not write:
  two groundings' truth values in one context assert nothing at all, and a labeling the
  sweep can no longer see is a leak that grows by one context per re-run.

  Asked twice, and both are worth their cost — a handful of index reads against a solve.
  Once at the top of `label`, so a run that cannot land fails before the solve rather
  than after it; once inside `clear-run!`, where the destruction actually happens, so
  the guarantee is local to the thing that needs it."
  [kb base into-cx]
  (let [{:keys [believed orphaned]} (blocked-artifacts kb base into-cx)]
    (when (or (seq believed) (seq orphaned))
      (throw (ex-info (str "a previous solve's artifacts under " into-cx
                           " cannot be replaced"
                           (when (seq believed)
                             (str "; believed sentexes in " (pr-str believed)))
                           (when (seq orphaned)
                             (str "; no labelingOf marker on " (pr-str orphaned)))
                           " — a solve clears only the inert content it wrote, so retract"
                           " what is believed there, retract the unmarked contexts and"
                           " their genlCx edges, or label into a different Into")
                      {:type :labeling-run-blocked
                       :into into-cx :base base
                       :believed believed :orphaned orphaned})))))

(defn- clear-context!
  "Retract `ctx`'s own extent — the labeling truth values and their marker, or a stale
  classification — and, with a `base`, the one `(genlCx ctx base)` edge a solve writes
  to place a labeling under it.  `retract!` tears an inert sentex down directly.

  Guarded: if anything in the extent is *believed*, `ctx` is not a solve artifact —
  everything a solve writes into its contexts is inert by construction — and nothing
  is touched.  The sweep must never destroy knowledge, whatever a context is named.

  The extent, and not everything that *mentions* `ctx`: the term index would also
  return a user's sentexes about the context, asserted from anywhere — a `genlCx` edge
  hanging it under a base of their own, a claim naming it — and the guard reads the
  extent, so it cannot tell those from the solve's.  So the edge is matched **whole**,
  against the base the run is placing this labeling under, rather than by its functor:
  a user is free to hang a labeling context under bases of their own, and those edges
  are theirs.  A classification context has no solve edge at all — hence the nil `base`
  — so every `(genlCx <Into>Class _)` in the KB is somebody else's, and an empty
  `<Into>Class` passes the believed-extent guard, which reads the extent and cannot
  see an edge.

  The guard is the second reading of the same question: `refuse-blocked-run!` asks it
  of every artifact before any of them is touched, so a run that would be blocked here
  never reaches here.  This one keeps the promise local to the destruction."
  [kb ctx base]
  (let [extent (stored-in kb ctx)]
    (when (not-any? #(jtms/in? (reasoning/tms kb) (:id %)) extent)
      (doseq [s extent]
        (wiring/retract-sentex kb (:id s)))
      (when base
        (doseq [{:keys [id sentence]} (kb/find-sentexes kb ctx)
                :when (= sentence (list 'genlCx ctx base))]
          (wiring/retract-sentex kb id))))))

(defn- clear-run!
  "Remove every artifact a previous `(do/label Base Into)` / `(do/classify Into)` left:
  the numbered labeling contexts, each with the `genlCx` edge that placed it under
  `base`, and the classification's extent.
  Replace-on-rerun is what keeps a run from accreting across groundings — an inert
  `(head)` beside an inert `(not head)` in one context asserts nothing — and
  retracting the placement edge is what drops a surplus stale context (a run
  that shrank from three labelings to two) out of the hierarchy, so `classify`
  cannot sweep it back in.  The labeling contexts are found by their ownership
  marker, so the edge taken off each is one the solve minted.

  Refuses rather than sweeps what it can: an artifact it cannot replace is one the
  next `classify` would read beside the new run's, so a partial sweep is worse than
  none (`refuse-blocked-run!`).  Nothing is retracted until every artifact has been
  checked."
  [kb base into-cx]
  (refuse-blocked-run! kb base into-cx)
  (doseq [ctx (labeling-contexts kb into-cx)]
    (clear-context! kb ctx base))
  (clear-context! kb (class-context into-cx) nil))

;; ---- grounding: assumptionRules × visible facts → choice heads -----------

(defn- assumption-rules
  "Every **believed** `assumptionRule` visible from `base` — scoped to `base` and its
  genlCx up-closure, never the whole KB.  `sentexes-in-context` reads storage, so
  the belief question is asked here, as both chainers ask it: a defeated or superseded
  assumptionRule must not mint choice heads.  `rule-believed?` rather than `jtms/in?`
  so an `:inert` rule stays available — this run is the fourth consumer of a rule's
  firing beside the three chainers, and it reads rules by the same rule they do."
  [kb base]
  (for [ctx (distinct (cons base (tax/context-up (reasoning/taxonomy kb) base)))
        s   (stored-in kb ctx)
        :when (and (rules/assumption? s) (res/rule-believed? kb (:id s)))]
    s))

(defn- registry-bounds
  "`res/prove` bounds whose **leaf is the prover registry**, so a grounding join reaches an
  antecedent a registered prover or evaluatable answers — a reachability partition, a
  computed relation, a transitive closure — and not only a stored fact.  `provers/solve-goal`
  answers every leaf (stored facts among them, through `FactProver`), and
  `registry-est-override` costs a prover-answered conjunct by the prover's own estimate, so
  the planner binds it last rather than enumerating an open relation.  This is the division
  `vaelii.core/query` runs: grounding runs it too, so a choice menu is derived from believed
  state the same way a rule reads it (docs/solving.md), instead of the caller pre-projecting
  the menu into stored candidate facts."
  [kb base]
  {:leaf-solver  provers/solve-goal
   :est-override (provers/registry-est-override kb base)})

(defn- ground-heads
  "The distinct ground choice heads: each assumptionRule's antecedents proved over the
  facts believed in `base` (a scoped, belief-filtered join), its head substituted with
  each solution's bindings.  The head must be a positive literal — `build` refuses a
  negated one (`:choice-head-not-positive`), since the labeling round-trip through
  `(not head)` would flip its polarity.

  The antecedents prove over a **registry leaf** (`registry-bounds`), so a candidate that
  rests on a registered prover — `(sameLandmass ?a ?b)` over a Clojure partition, an
  evaluatable — is a legal antecedent, not something the caller must pre-compute into
  stored candidate facts.

  A rule's `exceptWhen` guard is honored per binding, evaluated in `base` — grounding
  is a fourth consumer of a rule's firing beside the three chainers, and it makes the
  same decision they do (docs/exceptions.md): a choice the exception holds of is not
  offered.  That is what makes an exception the way to say \"this candidate is already
  ruled out\" declaratively, instead of the caller pre-filtering the menu."
  [kb base]
  (let [bounds (registry-bounds kb base)]
    (distinct
     (for [rsx (assumption-rules kb base)
           :let [ante  (vec (:antecedent rsx))
                 head  (:consequent rsx)
                 guard (provers/rule-guard kb rsx base)]
           binding (res/prove kb (fn [g] (provers/candidate-rules kb g base)) ante base bounds)
           :when (or (nil? guard) (guard binding))]
       (res/substitute head binding)))))

;; ---- constraints among the heads (MVP: direct only) ----------------------

(defn- negation-pair? [s1 s2]
  (or (= s1 (list 'not s2)) (= s2 (list 'not s1))))

(defn- functional-clash?
  "Two heads of a `functional` predicate that agree on the first argument but differ
  on the value — the constraint that makes `functional color` mean 'at most one'.

  The mark is read from `base`, the solving context: the explicit constraint rules beside
  these detectors are scoped to `base` (`constraint-rules`), so a `functional` declared in
  a context `base` cannot see must not forbid two of its choice heads either."
  [kb base s1 s2]
  (and (sequential? s1) (sequential? s2)
       (= 3 (count s1)) (= 3 (count s2))
       (= (first s1) (first s2))
       (= (second s1) (second s2))
       (not= (nth s1 2) (nth s2 2))
       (tax/has-prop? (reasoning/taxonomy kb) :functional (first s1) base)))

(defn- disjoint-clash?
  "Two unary type memberships of the same individual whose types are disjoint —
  disjointness read from `base`, for `functional-clash?`'s reason."
  [kb base s1 s2]
  (and (sequential? s1) (sequential? s2)
       (= 2 (count s1)) (= 2 (count s2))
       (= (second s1) (second s2))
       (not= (first s1) (first s2))
       (kb/disjoint? kb (first s1) (first s2) base)))

(defn- clash? [kb base s1 s2]
  (or (negation-pair? s1 s2)
      (functional-clash? kb base s1 s2)
      (disjoint-clash? kb base s1 s2)))

(defn- pairs [xs]
  (let [v (vec xs)]
    (for [i (range (count v)), j (range (inc i) (count v))] [(v i) (v j)])))

(defn- positive-core
  "A head's positive body — a `(not X)` unwrapped to X, else the head itself."
  [s]
  (if (and (seq? s) (= 'not (first s))) (second s) s))

(defn- clash-key
  "The bucket a head can clash within: the first argument of its positive body.  A
  negation pair, a functional clash, and a disjoint clash all require the two heads to
  agree on that argument, so heads with different keys can never clash — which turns the
  O(n²) all-pairs scan into O(Σ bucket²), flat when buckets are small (a node's three
  colours, say).  A head with no argument buckets under nil."
  [s]
  (let [p (positive-core s)]
    (when (and (sequential? p) (> (count p) 1)) (nth p 1))))

(defn- nogoods
  "The nogoods the auto-clash detectors find among the candidate heads (keyed by their
  program-local ids): one per clashing pair, uniform priority.  Heads are bucketed by
  `clash-key` and only compared within a bucket — the full pairwise `clash?` restricted
  to pairs that could possibly clash, so a 3-coloring's 30k choice heads cost O(nodes)
  rather than O(heads²).  The bucketing is content-derived and each bucket is sorted
  through `nm/print-key` — a bare `pr-str` would let an ambient `*print-length*` collapse
  the key and put the reported `(contradicts X Y)` pair in `head->id`'s map order — so
  the nogood set is order-independent."
  [kb base head->id]
  (for [bucket (vals (group-by (comp clash-key key) head->id))
        [[s1 _] [s2 _]] (pairs (nm/sort-by-content-key (comp nm/print-key key) compare bucket))
        :when   (clash? kb base s1 s2)]
    {:nogood #{(head->id s1) (head->id s2)}
     :priority 1
     :sentence (list 'contradicts s1 s2)}))

;; ---- constraint rules: a conjunctive nogood over facts + choice heads -----
;; A `set/hardConstraint` / `set/softConstraint` rule's body is a nogood template
;; mixing background facts and choice-head patterns.  Grounding it is a JOIN: the
;; background literals against the facts believed in `base`, the choice literals against
;; the ground choice heads.  Each satisfying binding yields the set of choice-head ids it
;; used — a model choosing all of them together is forbidden (hard) or penalized (soft).
;; This is what lets a constraint relate two *different* individuals (edge adjacency),
;; which the direct-clash detectors above — always one shared individual — cannot.

(defn- constraint-rules
  "Every **believed** constraint rule visible from `base` — scoped to `base` and its
  genlCx up-closure, and belief-filtered, like `assumption-rules`: a defeated or
  superseded constraint must not go on forbidding models.  A **cardinality** rule is a
  constraint rule too but grounds to a solver cardinality atom, not a conjunctive nogood,
  so `cardinality-rules` takes those and this excludes them."
  [kb base]
  (for [ctx (distinct (cons base (tax/context-up (reasoning/taxonomy kb) base)))
        s   (stored-in kb ctx)
        :when (and (rules/constraint? s) (not (rules/cardinality-of s))
                   (res/rule-believed? kb (:id s)))]
    s))

(defn- choice-arg-index
  "Index the ground choice heads for join lookup:
     :by-pred {pred [head …]}                 — every head of a predicate
     :by-arg  {[pred pos val] #{head …}}      — heads with `val` at 1-based arg `pos`
  A partially-ground choice literal is matched by intersecting the `:by-arg` sets for its
  ground argument positions (`literal-heads`) — so an edge×colour probe is a couple of
  set reads, not a scan of every head."
  [heads]
  (reduce
   (fn [idx head]
     (let [pred (first head)]
       (reduce (fn [idx [i a]]
                 (update-in idx [:by-arg [pred (inc i) a]] (fnil conj #{}) head))
               (update-in idx [:by-pred pred] (fnil conj []) head)
               (map-indexed vector (rest head)))))
   {}
   heads))

(defn- literal-heads
  "The choice heads a (partially ground) choice literal `lit` can match, via `idx` —
  intersect the `:by-arg` sets for its ground argument positions; with no ground
  argument, every head of the predicate."
  [idx lit]
  (let [pred   (first lit)
        ground (for [[i a] (map-indexed vector (rest lit))
                     :when (not (sx/variable? a))]
                 [pred (inc i) a])]
    (if (seq ground)
      (reduce set/intersection (map #(get-in idx [:by-arg %] #{}) ground))
      (get-in idx [:by-pred pred] []))))

(defn- join-choice-literals
  "Extend binding `b` (and its accumulated choice-head-id set `ids`) across the choice
  literals `chs`, matching each against `idx`.  Returns `[[binding ids] …]`."
  [idx head->id chs b ids]
  (if (empty? chs)
    [[b ids]]
    (let [lit (res/substitute (first chs) b)]
      (mapcat (fn [head]
                (when-let [b2 (res/unify lit head b)]
                  (join-choice-literals idx head->id (rest chs) b2 (conj ids (head->id head)))))
              (literal-heads idx lit)))))

(defn- neg-choice-lit?
  "A `(not <choice-literal>)` body literal — a choice head required to be *absent*.  A
  conjunction of these is an at-least-one requirement: `(not c1) (not c2) (not c3)`
  forbids a model in which all three are false, i.e. forces at least one true.

  The literal may be partially ground: `ground-constraint-body` joins it against the
  choice-head index like a positive one, so `(not (pick ?c))` on its own means *every*
  pick, one nogood each."
  [choice-preds l]
  (and (seq? l) (= 'not (first l)) (sequential? (second l))
       (choice-preds (first (second l)))))

(defn- ground-constraint-body
  "Join `body` over the facts believed in `base` (background literals) and the ground
  choice heads (positive choice literals — predicate in `choice-preds`), carrying any
  *negated* choice literals `(not <choice>)` through as a set of choice-head ids
  required-absent.  Returns `[[#{pos-ids} #{neg-ids} marker] …]`, one per satisfying
  binding.

  Background literals are solved together through the ordinary conjunctive prover
  (`res/prove` over a **registry leaf** — `bounds`, so a background literal a prover or
  evaluatable answers joins like `ground-heads`' antecedents do — belief-filtered and
  cost-planned); each solution is extended across the positive choice literals against the
  choice-head index, and then across the negated ones the same way.  Literals are classified
  by predicate — a body predicate naming a choice head is a choice literal, everything else a
  background fact — the modeling contract for a constraint body.  Negated *background*
  literals are out of scope.

  **The negated literals are joined, not merely substituted.**  They are removed from
  `rest-body` before the positive join, so nothing else binds their variables: a
  substitution-only lookup would find no head for `(not (pick ?c))`, drop the binding,
  and contribute no nogood — the at-least-one idiom in `neg-choice-lit?`'s own
  docstring, failing open and in silence.  Joining them against the same index the
  positive literals use grounds `?c` over every head the predicate has, one nogood per
  combination, which is what the idiom means.  A literal matching *no* head drops its
  binding rather than constraining anything, which the join gives for free and is the
  right answer regardless: an atom that does not exist is absent in every model, so it
  can never be false-*together* and the requirement it guards is vacuous.

  Order matters and is fixed here: positives first, so a variable shared with the
  background or a positive literal is already bound when the negated ones are reached."
  [kb base body consequent choice-preds head->id idx bounds]
  (let [neg?        #(neg-choice-lit? choice-preds %)
        neg-lits    (mapv second (filter neg? body))
        rest-body   (remove neg? body)
        choice-lit? #(and (sequential? %) (choice-preds (first %)))
        bg  (remove choice-lit? rest-body)
        chs (filter choice-lit? rest-body)]
    (for [bgb          (if (seq bg) (res/prove kb (fn [g] (provers/candidate-rules kb g base)) (vec bg) base bounds) [{}])
          [b ids]      (join-choice-literals idx head->id chs bgb #{})
          [b2 neg-ids] (join-choice-literals idx head->id neg-lits b #{})
          :when        (or (seq ids) (seq neg-ids))]
      [ids neg-ids (res/substitute consequent b2)])))

(defn- check-minimize-weight
  "Throw `:not-well-formed` unless `weight` — the ground weight one binding of the
  `asp/minimize` rule `rsx` read off a background fact — is an integer inside the solver's
  32-bit weight range.  The ASPIF writer prints the weight unchanged, and a backend handed
  a `2.5` or a symbol rejects the whole program as `:solver-failed :status :unknown`, a
  report that names no fact."
  [rsx weight]
  (when-not (and (integer? weight) (<= Integer/MIN_VALUE weight Integer/MAX_VALUE))
    (let [surface (rules/rewrap (sx/sentence-of rsx) nil nil nil (rules/constraint-of rsx))]
      (throw (ex-info (str "an asp/minimize weight must be an integer in the solver's 32-bit "
                           "range; a background fact bound " (pr-str weight) " in "
                           (pr-str surface))
                      {:type :not-well-formed :sentence surface :weight weight})))))

(defn- constraint-nogoods
  "Ground every constraint rule visible from `base` into nogoods, one per satisfying
  binding of its body.  A positive body yields a `:nogood` (those choice heads forbidden
  to hold together); a negated-choice body yields a `:neg` (forbidden to be absent
  together — an at-least-one).  A `set/hardConstraint` rule's nogoods carry `:hard true`
  (an integrity constraint — a violating model is excluded outright); a
  `set/softConstraint` rule's are minimized like the auto-detector's."
  [kb base head->id]
  (let [choice-preds (into #{} (map first) (keys head->id))
        idx          (choice-arg-index (keys head->id))
        bounds       (registry-bounds kb base)]
    (for [rsx (constraint-rules kb base)
          :let [body   (vec (:antecedent rsx))
                conseq (:consequent rsx)
                hard?  (= :hard (rules/constraint-of rsx))]
          [ids neg-ids marker] (ground-constraint-body kb base body conseq choice-preds head->id idx bounds)
          ;; a soft's ground consequent marker may carry an objective level and a per-head
          ;; weight (`asp/minimize` / a priority-tagged soft); an ordinary soft reads back
          ;; level 1, unit weight (rules/soft-cost-of), so nothing changes for the rest
          :let [{:keys [priority weight marker]} (rules/soft-cost-of marker)
                _ (when (some? weight) (check-minimize-weight rsx weight))]]
      (cond-> {:nogood ids :priority priority :sentence (list 'contradicts marker)}
        weight        (assoc :weight weight)
        (seq neg-ids) (assoc :neg neg-ids)
        hard?         (assoc :hard true)))))

;; ---- cardinality rules: a bound over a whole set of choice heads ----------
;; A `asp/atMost` / `asp/atLeast` rule (`rules/normalize-cardinality`) grounds NOT to a
;; nogood per binding but to ONE cardinality entry per group: its pattern is matched
;; against every ground choice head, the matches are grouped by the pattern's variables
;; OTHER than the counted one, and each group becomes a bound over that group's heads.
;; `edge/translate` renders each as a single weight-body statement, which is what turns
;; the `C(n, k+1)` subset expansion into O(n) (docs/solving.md).

(defn- cardinality-rules
  "Every **believed** cardinality rule visible from `base` — the `constraint-rules`
  counterpart for the rules that carry a `cardAtMost` / `cardAtLeast` marker."
  [kb base]
  (for [ctx (distinct (cons base (tax/context-up (reasoning/taxonomy kb) base)))
        s   (stored-in kb ctx)
        :when (and (rules/cardinality-of s) (res/rule-believed? kb (:id s)))]
    s))

(defn- cardinality-constraints
  "Ground every cardinality rule visible from `base` into `solve/Program` cardinality
  entries.  The rule's pattern (its single antecedent) is matched against the ground
  choice heads; each match binds the counted variable and the group variables, and the
  matches are grouped by the group binding — so `(empireBuild ?c transport)` counted over
  `?c` is one global group, and `(empireFerry ?a ?t)` counted over `?a` is one group per
  `?t`.  Each group yields one entry over the heads it collected.

  A **global** bound — its pattern has no variable other than the counted one — is one
  group even when it matches no head: an `asp/atLeast` over an empty global group is
  infeasible (there are not `k` of nothing), which `edge/card-encoding` reports as a
  program with no model, rather than silently dropping the floor.  A **grouped** bound
  keeps the grounder's reading instead: only the groups some head realizes exist, so a
  group binding no head mentions holds vacuously, the way a universally-quantified
  constraint over an empty domain does.  A group that exists but is smaller than `k` is
  infeasible under either, which `edge/card-encoding` reports the same way."
  [kb base head->id]
  (let [idx (choice-arg-index (keys head->id))]
    (for [rsx (cardinality-rules kb base)
          :let [{:keys [op k counted]} (rules/cardinality-of rsx)
                hard?      (= :hard (rules/constraint-of rsx))
                pattern    (first (:antecedent rsx))
                group-vars (remove #{counted}
                                   (distinct (filter sx/variable?
                                                     (tree-seq sequential? seq pattern))))
                matches    (for [head (literal-heads idx pattern)
                                 :let  [b (res/unify pattern head {})]
                                 :when b]
                             [(dissoc b counted) (head->id head)])
                ;; A global bound (no group variables) is ONE group even with no match, so
                ;; its empty-member entry can be reported infeasible; a grouped bound is
                ;; only the groups a head realizes.
                groups     (if (and (empty? matches) (empty? group-vars))
                             {{} []}
                             (group-by first matches))]
          [gkey members] groups]
      {:op op :k k
       :members  (into #{} (map second) members)
       :hard     hard?
       :priority 1
       :sentence (list 'cardinalityBound op k (res/substitute pattern gkey))})))

;; ---- the program ---------------------------------------------------------

(defn- build
  "Ground the choices **in memory**, detect the constraints among them (both the direct
  auto-clashes and the ground constraint-rule bodies), and build the Program.  Returns
  `{:program p :head->id {sentence id}}` or nil when there are no choices to make — and
  writes nothing, so a solve that goes on to fail (no backend) has no side effects to
  undo.

  The ids are program-local, minted over the content-sorted heads — never KB handles.
  Nothing needs more: `solve/content-key` orders by sentence + context, and an atom
  label is only ever read back within the solve that minted it.  Storing the menu
  instead would leave write-only sentexes nothing maintains — see the ns docstring,
  \"What persists, and what does not\".

  **This sort is the whole of the id assignment**, so it is the one ordering a
  labeling can be traced back to: `edge/translate` builds the choice order, the nogood
  bodies, the minimize weights and the level-0 tiebreak off these ids.  The key is
  printed through `nm/print-key` for that reason — a bare `pr-str` under an ambient
  `*print-length*` elides two long choice heads to one prefix, and the tie falls back to
  `ground-heads`' own order, which is `matches-visible` set order over handles.  Two KBs
  holding one body of knowledge would then mint different ids and the solver could
  return a different labeling."
  [kb base]
  (let [heads (nm/sort-by-content-key nm/print-key compare (ground-heads kb base))]
    ;; A choice head must be a **positive** literal.  A labeling persists `(head)` for a
    ;; chosen-true choice and `(not head)` for a chosen-false one, and `classify`'s
    ;; `polarity-table` reads that back by unwrapping one `not` — so a negated head
    ;; `(not X)` would round-trip as its positive core `X` with the polarity flipped, and
    ;; `classify` would emit a statement about a non-head (docs/solving.md).  Refuse it
    ;; here, before any world is written, rather than misclassify it silently.
    (when-let [neg (seq (filter #(and (seq? %) (= 'not (first %))) heads))]
      (throw (ex-info (str "a choice head must be a positive literal; negated assumptionRule "
                           "head(s): " (pr-str (vec neg)))
                      {:type :choice-head-not-positive :negated (vec neg) :base base})))
    (when (seq heads)
      (let [head->id (into {} (map-indexed (fn [i s] [s (inc i)])) heads)
            content  (into {} (map (fn [[s id]] [id {:sentence s :context base}])) head->id)
            ngoods   (concat (nogoods kb base head->id)
                             (constraint-nogoods kb base head->id))
            cards    (cardinality-constraints kb base head->id)
            program  (solve/program (set (vals head->id)) ngoods content cards)]
        {:program program :head->id head->id}))))

;; ---- do/label: one inert labeling context per optimal answer set ---------

(defn- one-optimum
  "One answer set as `[kept-set]`, or nil with no ASP backend — the single-labeling
  counterpart to `edge/enumerate-optima`, split by phase for a caller that wants to time
  grounding against solving.

  `keep-belief?` chooses the objective: on, the solve minimizes defeated assumptions
  (one *optimal* answer, keeping as much belief as possible); off, it is plain
  satisfaction (one *satisfying* answer, no optimization), which is the difference
  between finishing and not at scale.  Tiebreak is always off here — its per-atom
  objective is its own scaling wall, and singling out one of many valid answers is not
  wanted; the content-keyed program is order-independent and clingo deterministic, so
  one solve is a stable answer regardless.  Returns `{:optima [#{ids}] :best-effort? b
  :translate-ms t :solve-ms t}`, or `{:optima nil}` — `:best-effort?` true when the solve
  was cancelled with a model still in hand (its optimality unproven; `edge/kept-of` reads
  it as an answer anyway).

  **An `:unsat` program yields NO answer set — `[]`, not `[#{}]`.**  The two read
  identically off `kept-of`, which correctly keeps nothing either way, and the
  difference is everything: `[#{}]` is *one world, in which every choice is false*,
  which for a program whose hard constraints admit no model is a world violating them.
  Exactly what a hard at-least-one forbids, reported as the answer to it.
  `enumerate-optima` makes the same distinction by construction, which is why `:all`
  already reports nothing here."
  [program keep-belief?]
  (if-not (solver/available?)
    {:optima nil}
    (let [ta         (System/nanoTime)
          translated (edge/translate program {:tiebreak? false :keep-belief? keep-belief?})
          tb         (System/nanoTime)
          ;; the backend reads whether the program has an objective: with none (`:sat` and
          ;; no soft constraint) it stops at the first model, and with one it streams
          ;; improving models, which a soft constraint under `:sat` still needs
          result     (solver/solve translated :label)
          tc         (System/nanoTime)]
      {:optima       (if (= :unsat (:status result)) [] [(edge/kept-of translated result)])
       ;; a cancelled optimization that still had a model: the labeling is valid but its
       ;; optimality went unproven, so the caller is told (edge/kept-of read it anyway).
       :best-effort? (= :best-effort (:status result))
       :translate-ms (/ (- tb ta) 1e6)
       :solve-ms     (/ (- tc tb) 1e6)})))

(defn label
  "Ground the `assumptionRules` visible from `Base` (honoring their `exceptWhen`
  guards), detect the constraints among the ground choice heads — the direct
  auto-clashes *and* every `set/hardConstraint` / `set/softConstraint` rule's body
  ground into a nogood — and solve.

  **`mode` (an optional third argument, default `:all`) picks how many worlds:**

    * `:all` — enumerate **every** optimal answer set and materialize each as its own
      inert labeling context: a `genlCx` child of `Base` named
      `<Into><i>` (skipping any slot an unrelated context occupies) holding
      `(head)` for a chosen-true choice, `(not head)` for a chosen-false one, and its
      `labelingOf` ownership marker.  The worlds coexist and persist for `do/classify` to
      aggregate; base belief is untouched.  This is the studying-many-worlds mode, and it
      is infeasible where the optima are astronomically many (a large graph coloring has
      too many valid colorings to enumerate).
    * `:one` — commit to **one** optimal answer set via a single `:label` solve
      (minimizing defeated assumptions — keep as much belief as possible), and return it
      in the result **without persisting anything**.  The solving mode: it wants an
      answer, not an artifact, so it is feasible at scale (one solve, no enumeration, no
      materialization).  `Into` is accepted for a uniform imperative shape but unused.
    * `:sat` — `:one`, but plain **satisfaction** rather than optimization: no
      keep-belief objective, so clingo stops at the first model instead of proving
      cost-optimality over the choice atoms.  For a program whose hard constraints
      already pin what must be chosen (a graph coloring's hard at-least-one), \"keep as
      much as possible\" is redundant and the optimization is a scaling wall — `:sat`
      finishes where `:one` does not.  Same shape as `:one` (returns one labeling,
      persists nothing).

  **Replace-on-rerun (`:all` only).**  A previous `:all` run's artifacts under `Into`
  are cleared before new ones are written, so re-running after the base moved converges
  instead of accreting.  A run that grounds *no* choices clears too.  The one exception
  is `:no-backend` — nothing was computed, so the previous artifact is left standing.

  **A run that cannot replace what is there refuses** (`:labeling-run-blocked`), before
  the solve rather than after it.  Two things stop a sweep: a labeling context somebody
  has asserted *believed* content into, which the sweep rightly declines to destroy, and
  one whose `labelingOf` marker has been retracted, which the sweep can no longer find.
  Proceeding past either leaves two groundings' artifacts under one `Into` — a
  `classify` aggregating worlds from different solves, and a `genlCx` edge nothing will
  ever retract.  `refuse-blocked-run!` names what is in the way; retracting that
  context's extent, or naming a different `Into`, clears it.

  The grounding is never stored; `:choices` is the menu in content order (see `build`).
  Phase timings (`:ground-ms` = grounding the Program, `:translate-ms` = rendering ASPIF,
  `:solve-ms` = the solve) ride the result for a profiling caller.

  Returns `{:base :into :choices [..] :labelings [{:context :true [..] :false [..]}]
  :count n}` (`:context` nil in `:one` mode, which persists nothing).  A `:one`/`:sat`
  result also carries `:best-effort? true` when the solve was cancelled at the time
  limit with a model in hand — a valid labeling whose optimality went unproven (the key
  is absent otherwise).  `:count 0` with
  a `:reason` when there is no labeling to report: `:no-choices` (nothing was ground),
  `:no-backend` (nothing could be solved), or `:unsatisfiable` — the hard constraints
  admit no model, so there is no world to hand back.  Under `:all` an unsatisfiable
  program simply enumerates nothing and reports `:count 0` without a reason, the
  materialization loop having nothing to run."
  ([kb base into-cx] (label kb base into-cx :all))
  ([kb base into-cx mode]
   ;; `:one` and `:sat` return a labeling and persist nothing, so they have nothing to
   ;; replace and nothing to sweep — only `:all` writes, and the refusal comes before
   ;; the grounding rather than after the solve
   (let [single? (contains? #{:one :sat} mode)
         _       (when-not single? (refuse-blocked-run! kb base into-cx))
         t0      (System/nanoTime)
         built   (build kb base)
         t1      (System/nanoTime)]
     (if-let [{:keys [program head->id]} built]
       (let [id->head (zipmap (vals head->id) (keys head->id))
             all-ids  (set (vals head->id))
             ;; the heads in the order `build` minted their ids (a `nm/print-key` sort over the
             ;; same set), read straight off `id->head` — no re-sort, no second key built
             choices  (mapv id->head (range 1 (inc (count head->id))))
             {:keys [optima translate-ms solve-ms best-effort?]}
             (if single?
               (one-optimum program (= mode :one))     ; :sat ⇒ keep-belief off (plain SAT)
               (let [ta (System/nanoTime), o (edge/enumerate-optima program)]
                 {:optima o :solve-ms (/ (- (System/nanoTime) ta) 1e6)}))
             timing   {:ground-ms (/ (- t1 t0) 1e6) :translate-ms translate-ms :solve-ms solve-ms}
             labeling (fn [chosen] {:true  (into [] (map id->head) chosen)
                                    :false (into [] (map id->head) (remove (set chosen) all-ids))})]
         (cond
           (nil? optima)
           (merge {:base base :into into-cx :count 0 :choices choices
                   :reason :no-backend :labelings []} timing)

           ;; no answer set at all: the hard constraints admit no model.  Under `:all`
           ;; that falls out of enumerating nothing; under `:one` / `:sat` it has to be
           ;; said, or the empty labeling is indistinguishable from a world in which every choice is
           ;; false — which is itself a world the constraints exclude.
           (and single? (empty? optima))
           (merge {:base base :into into-cx :count 0 :choices choices
                   :reason :unsatisfiable :labelings []} timing)

           ;; :one / :sat — return the single labeling, persist nothing.  `:best-effort?`
           ;; rides along when the solve was cancelled with a model in hand (unproven
           ;; optimal); absent otherwise, so a caller that ignores it sees no change.
           single?
           (merge {:base base :into into-cx :count 1 :choices choices
                   :labelings [(assoc (labeling (first optima)) :context nil)]}
                  (when best-effort? {:best-effort? true})
                  timing)

           ;; :all — materialize each optimum as its own inert labeling context
           :else
           (do
             (clear-run! kb base into-cx)
             (let [ctxs (free-labeling-contexts kb into-cx (count optima))]
               (merge {:base base :into into-cx :count (count optima) :choices choices
                       :labelings
                       (vec (map-indexed
                             (fn [i chosen]
                               (let [ctx    (nth ctxs i)
                                     l      (labeling chosen)
                                     truths (:true l)
                                     falses (:false l)]
                                 ;; a genlCx edge so the labeling shows under Base in the tree;
                                 ;; monotonic because it is a real structural edge, not a solve result
                                 (wiring/assert-sentence kb (list 'genlCx ctx base) base {:strength :monotonic})
                                 ;; the ownership marker rediscovery reads (see labeling-contexts)
                                 (kb/find-or-create-sentex kb (list 'labelingOf ctx into-cx (inc i)) ctx)
                                 (doseq [s truths] (kb/find-or-create-sentex kb s ctx))
                                 (doseq [s falses] (kb/find-or-create-sentex kb (list 'not s) ctx))
                                 (assoc l :context ctx)))
                             optima))}
                      timing)))))
       (do (when-not single? (clear-run! kb base into-cx))
           {:base base :into into-cx :count 0 :choices []
            :reason :no-choices :labelings []})))))

;; ---- do/classify: gather brave/cautious over the labelings ---------------

(defn- polarity-table
  "One labeling context's extent as a map from choice head to the polarity it
  records — `:true` for `(head)`, `:false` for `(not head)`; the ownership marker
  is skipped.  **One extent read per context**: reading the whole extent once per
  labeling and answering every (context, head) probe from the map keeps classify's
  store traffic linear rather than quadratic in the solve's size.  A head absent from
  the map (nil) is a labeling that says nothing about it, which classifies as
  `:supportable` below."
  [kb ctx]
  (into {}
        (keep (fn [{:keys [sentence]}]
                (cond
                  (marker? sentence) nil
                  (and (seq? sentence) (= 'not (first sentence))) [(second sentence) :false]
                  :else [sentence :true])))
        (stored-in kb ctx)))

(defn classify
  "Gather brave/cautious over the labelings a prior `(do/label _ Into)` produced, and
  record the result as inert sentexes in `<Into>Class`.  A choice head is

    * `(forced H)`      — `(head)` in **every** labeling (a cautious/skeptical consequence),
    * `(excluded H)`    — `(not head)` in every labeling,
    * `(supportable H)` — otherwise (a brave/credulous consequence only).

  Pure aggregation over the persisted labeling contexts — no solver, no whole-KB scan,
  and **one extent read per labeling** (`polarity-table`), with everything after in
  memory.  Its own previous classification is cleared first (replace-on-rerun,
  same discipline as `label`): a stale classification describes labelings that no
  longer exist.  A `<Into>Class` holding *believed* content is one the sweep declines
  to touch, so the run refuses (`:labeling-run-blocked`) rather than write a second
  classification beside the first.  Returns
  `{:class-context :forced [..] :supportable [..] :excluded [..]}`, or `:count 0`
  `:reason :no-labelings` when `label` was never run for `Into`."
  [kb into-cx]
  (let [labelings (labeling-contexts kb into-cx)
        klass     (class-context into-cx)]
    (when (believed-extent? kb klass)
      (throw (ex-info (str "the classification under " klass " cannot be replaced — "
                           klass " holds believed sentexes, and a classify sweep clears"
                           " only the inert content it wrote.  Retract what is believed"
                           " there, or classify into an Into other than " into-cx)
                      {:type :labeling-run-blocked :into into-cx
                       :believed [klass] :orphaned []})))
    (if (empty? labelings)
      {:into into-cx :count 0 :reason :no-labelings
       :forced [] :supportable [] :excluded []}
      (let [tables (mapv #(polarity-table kb %) labelings)
            heads  (distinct (mapcat keys tables))
            classify-one
            (fn [s]
              (let [ps (map #(get % s) tables)]
                (cond (every? #(= :true %) ps)  :forced
                      (every? #(= :false %) ps) :excluded
                      :else                     :supportable)))
            grouped (group-by classify-one heads)]
        (clear-context! kb klass nil)
        (doseq [[k ss] grouped, s ss]
          (kb/find-or-create-sentex kb (list (symbol (name k)) s) klass))
        {:into into-cx :class-context klass :count (count labelings)
         :forced      (vec (:forced grouped))
         :supportable (vec (:supportable grouped))
         :excluded    (vec (:excluded grouped))}))))
