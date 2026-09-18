;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.edge
  "The real ASP backend behind `vaelii.impl.types.solve/Solver` — the edge solver.

  `solve.clj` describes *what* an edge solve is: most of the KB is monotonic or
  default-true with no conflict, so only the contested defeasible nodes are sent,
  known-true content is fixed background, and contradictions are soft and
  prioritized so a solve never fails.  This namespace renders that `Program` to
  ASPIF and reads an answer set back.

  ## The encoding

  Each contested assumption is a **choice atom**: true means believed, false means
  defeated.  Known-true (`:fixed`) members of a contradiction are *not* atoms —
  they hold by assumption, which is exactly what makes them background.

  A contradiction `#{h1 h2 ...}` becomes a violation atom derived from its
  contested members:

      v :- a_h1, a_h2, ...

  and a **weak** constraint minimizing `v`.  Weak rather than hard is the whole
  point: an unsatisfiable contradiction costs, it does not make the program UNSAT,
  so it comes back in `:violated` instead of throwing.

  A nogood carrying `:hard true` (a `set/hardConstraint` rule ground by
  `solve-context`) is instead a **hard integrity constraint**

      :- a_h1, a_h2, ...

  with no violation atom and no minimize term: a model satisfying its whole body is
  excluded outright.  That is what makes graph 3-coloring plain satisfaction rather
  than optimality-proving over soft violations — an adjacency clash is never
  tradeable.  Soft nogoods (the default) keep the minimize path above.

  A **cardinality** entry (`program`'s `:cardinalities`, ground from a `asp/atMost` /
  `asp/atLeast` rule) is a bound on how many of a set of choice heads may or must hold,
  rendered as ONE weight-body statement rather than the `C(n, k+1)` subset nogoods a
  hand-written encoding needs.  A hard bound is a weight-body integrity constraint

      :- k+1 <= #count{ a_m1, a_m2, ... }        # at-most-k: never k+1 together

  a soft one derives a violation atom the same minimize path penalizes

      v :- k+1 <= #count{ ... }                  # breaching the bound costs, not excludes

  and at-least-`k` is the mirror over the default-negated members (`card-encoding`).

  In practice `:violated` comes back empty, and that is correct rather than a gap.
  An irreducible known-true clash never reaches a solver: `core/settle`'s
  `decide-nogood` classifies it as *hard* and reports it directly, and
  `solve/program` drops any nogood with no contested member.  What does arrive
  always has a contested member, and defeating that member always satisfies it.
  The `:doomed` path below is therefore defensive — it adds no work and stays
  correct if nogoods ever grow beyond today's `S` vs `(not S)` pairs.

  ## The objective, most significant first

  Higher ASPIF minimize priorities dominate lower ones, so the levels are:

  | level | minimizes | why |
  |---|---|---|
  | `2 + rank(p)` | violation atoms | satisfy contradictions, caller priority first |
  | `1` | defeated assumptions | give up as little belief as possible |
  | `0` | a content-keyed weight | break remaining ties *stably* |

  Caller priorities are mapped through their ascending rank rather than used as
  levels directly, so any integers work and none can collide with the two levels
  below.

  ## Determinism

  A tie between equally-good answer sets has no principled winner, but it must not
  depend on assertion order — the engine-wide invariant in docs/nmtms.md.  Atom ids
  are allocated in `solve/content-key` order, and level 0 weights defeating the
  greatest content-key most cheaply, mirroring the stub's choice.  Same knowledge
  in any order, same answer set.

  ## Availability

  `edge-solver` degrades rather than fails **when there is no backend at all**: with no
  clingo and no clasp reachable it delegates to `solve/local-solver`, so installing it is
  always safe.  Degradation is confined to that case on purpose — see below.

  ## A result that is not an answer

  A backend's result is an answer set only at `:optimum` or `:sat`.  `:interrupted`
  (the time limit, `config/asp-time-limit`, or a signal) and `:unknown` carry **no**
  witness, and every reader here maps an atom's absence to *defeated* or *not kept* —
  so read as an answer, an empty result defeats every contested assumption and labels
  every choice head false.  `answered?` gates each reader.

  **With a backend present, `edge-solver` decides nothing rather than degrading.**  The
  stub and ASP disagree — measured on two nogoods sharing a member, the stub defeats
  `{1,3}` where the optimum defeats `{2}` — and the two are not interchangeable halves of
  one answer.  A labeling solve that runs out of budget while the classification solve
  beside it finishes would pair a stub labeling with an ASP classification, which
  `label/check-agrees` reports as `:labeling-inconsistent`, blaming the encoding for a
  disagreement the fallback introduced.  Worse across a settle's defeat rounds: round 1
  interrupted and round 2 not yields a belief set neither solver would produce, differing
  run to run on identical knowledge — the order-independence invariant in docs/nmtms.md
  is a claim about *knowledge*, and a wall clock is not knowledge.  So `undecided` is
  returned instead: no defeat, the contested assumptions all stand, and `:error` names
  what went wrong for a caller that can act on it.  With no backend the two degrade
  together and stay consistent for free — `classify-program` claims nothing without one —
  which is why that case, and only that case, still falls back.

  A backend that **throws** — clingo's `:solver-failed`, clasp's `:solver-unavailable`,
  a JNA `Error` against a missing libclingo — reads the same way, and the catch is here
  rather than at the caller because this is the boundary a native failure crosses.  Left to
  propagate it would unwind whatever arbitration was in progress: `settle`'s
  `resolve-contradictions` calls the solver *after* an earlier round already mutated the
  TMS, so the throw would leave a half-arbitrated KB behind — stale `:conflicts`,
  `settle-finish` never reached, `reset-touched!` never run.  `undecided` leaves the KB
  as the round found it and hands the failure back as data.

  `:unsat` is different and keeps its own reading: a definite *no model*, the same answer
  in every run, so it costs the invariant nothing.  Each reader has a word for it —
  `edge-solver` degrades, `kept-of` keeps nothing, `enumerate-optima` is empty.

  The imperative readers (`kept-of`, `enumerate-optima`, `classify-program`) refuse an
  unanswered result with `:solver-failed` rather than return a world nobody computed.
  They are not mid-arbitration, so a throw there adds no work and says more."
  (:require
   [taoensso.trove :as trove]
   [vaelii.impl.asp.aspif :as aspif]
   [vaelii.impl.asp.atoms :as atoms]
   [vaelii.impl.asp.solver :as solver]
   [vaelii.impl.naming :as nm]
   [vaelii.impl.solve :as solve]
   [vaelii.impl.types.solve :as solve-types]))

;; Objective levels.  Violations sit above both, at 2 + the rank of the caller's
;; priority; these two are the fixed floor.
(def ^:private level-defeat-count 1)
(def ^:private level-tiebreak 0)

(defn- descriptor
  "The contradiction descriptor `atoms/intern-contradiction!` interns: a
  sentence-shaped value carrying the involved handles, so a witness atom can be
  read back without a secondary lookup."
  [{:keys [nogood sentence]}]
  (list 'contradiction sentence :involved (mapv (fn [h] [:sentex h]) (sort nogood))))

(defn- card-descriptor
  "The violation descriptor for a soft cardinality entry — the same shape
  `descriptor` gives a soft nogood, tagged `cardinality` and carrying every member."
  [{:keys [op k members sentence]}]
  (list 'cardinality (or sentence (list op k)) :involved (mapv (fn [h] [:sentex h]) (sort members))))

(defn- card-encoding
  "The weight body a cardinality entry over `member-atoms` (sorted atom ids) becomes,
  or a keyword for the two degenerate cases.  Returns

      [lower-bound weighted-literals]   a weight body of that bound
      :vacuous                          every model meets the bound — emit nothing
      :infeasible                       no model meets the bound — a model is impossible

  at-most-`k` forbids the count reaching `k+1`, over the positive literals; `k >= n`
  cannot be reached, so it is vacuous.  at-least-`k` forbids `n-k+1` of them being absent,
  over the default-negated literals; `k <= 0` is met by every model, `k > n` (or an empty
  member set with `k >= 1`) by none."
  [op k member-atoms]
  (let [n (count member-atoms)]
    (case op
      :at-most  (if (>= k n) :vacuous
                    [(inc k) (mapv (fn [a] [a 1]) member-atoms)])
      :at-least (cond (<= k 0) :vacuous
                      (> k n)  :infeasible
                      :else    [(- (inc n) k) (mapv (fn [a] [(- a) 1]) member-atoms)]))))

(defn translate
  "Render `program` to ASPIF.  Returns

      {:aspif      text or nil          ; nil when there is nothing to solve
       :stmts      [statement ...]      ; the structured program the clingo backend injects
       :table      the atom table
       :by-label   {label nogood}       ; violation atom -> the contradiction
       :assumptions [handle ...]        ; in content-key order
       :doomed     [nogood ...]}        ; all-fixed, unsatisfiable without solving

  `:tiebreak?` (default true) emits the level-0 content-keyed objective that makes
  the optimum unique.  Solving for *one* labeling wants it — an arbitrary choice
  still has to be a stable one.  Enumerating optima wants it **off**: it is an
  arbitrary preference, not a semantic constraint, and leaving it in collapses every
  tie to a single answer set, which would report a genuinely open choice as forced.
  `label/classify-program` is the caller that turns it off.

  `:keep-belief?` (default true) emits the level-1 objective that minimizes defeated
  assumptions — keep as much belief as possible.  Turning it **off** makes the solve
  plain *satisfaction* rather than optimization: with no minimize term clingo stops at
  the first model instead of proving cost-optimality over the choice atoms, which is
  the difference between finishing and not at scale (a 10k-node graph 3-coloring).  A
  caller turns it off only when the program's hard constraints already pin what must be
  chosen (e.g. a hard at-least-one), so \"keep as much as possible\" adds nothing."
  ([program] (translate program {}))
  ([{:keys [assumptions contradictions] :as program}
    {:keys [tiebreak? keep-belief?] :or {tiebreak? true keep-belief? true}}]
   (let [ordered   (nm/sort-by-content-key #(solve/content-key program %) compare assumptions)
         ;; the nogoods too: `settle` hands them in arrival order, and every emission
         ;; below — the violation-atom interning, the constraints, the minimize and
         ;; show statements — walks this seq, so an unsorted one renders two logically
         ;; identical programs as different ASPIF text and (without the tiebreak) two
         ;; different first-found optima for one KB.  The key is a COMPARABLE STRUCTURE
         ;; (a vector `compare` orders directly), not a printed string, and it is built
         ;; ONCE per nogood here — not by the sort's key fn, which `sort-by` re-invokes
         ;; on every comparison.  A printed key computed in the sort would do both: it
         ;; re-renders the whole nogood and re-`content-key`s every member, O(n log n)
         ;; times over the nogood set, which measures ~12× slower to ground a large
         ;; 3-colouring than leaving the nogoods in arrival order does.
         contradictions (let [ck #(solve/content-key program %)]
                          (->> contradictions
                               (map (fn [ng]
                                      [[(vec (sort (map ck (concat (:nogood ng) (:neg ng)))))
                                        (:priority ng)
                                        (boolean (:hard ng))]
                                       ng]))
                               (sort-by first)
                               (mapv second)))
         ;; Cardinality entries sorted the same content-keyed way, for the same reason:
         ;; every emission below walks this seq, so an unsorted one renders two logically
         ;; identical programs as different ASPIF text.
         cardinalities (let [ck #(solve/content-key program %)]
                         (->> (:cardinalities program)
                              (map (fn [c]
                                     [[(vec (sort (map ck (:members c))))
                                       (name (:op c)) (:k c)
                                       (boolean (:hard c)) (:priority c 1)]
                                      c]))
                              (sort-by first)
                              (mapv second)))
         n         (count ordered)
         table     (atoms/new-table)
         ;; Allocate in content-key order so atom ids never depend on assertion order.
         atom-of   (into {} (map (fn [h] [h (atoms/intern-sentex! table h)])) ordered)
         ;; Sorted by atom id — and therefore by content, since that is how atoms were
         ;; allocated.  A nogood's members are sets, so an unsorted body would put
         ;; literals in hash order and render two logically identical programs as
         ;; different text.  `pos` are members forbidden to hold together (`:nogood`);
         ;; `neg` are members forbidden to be absent together (`:neg`, e.g. an
         ;; at-least-one), emitted as default-negated literals.
         pos       (fn [ng] (sort-by atom-of (filter assumptions (:nogood ng))))
         neg       (fn [ng] (sort-by atom-of (filter assumptions (:neg ng))))
         involved  (fn [ng] (concat (pos ng) (neg ng)))
         ;; A fixed `:neg` member is an assumed-true one: its default-negated literal
         ;; is false, so the body can never hold and the nogood constrains nothing.
         ;; Dropping only the member instead would *tighten* the constraint — models
         ;; nothing forbade would be excluded, or penalized.
         vacuous?  (fn [ng] (not-every? assumptions (:neg ng)))
         grounded  (remove vacuous? contradictions)
         doomed    (filterv (comp empty? involved) grounded)
         live      (remove (comp empty? involved) grounded)
         ;; A `:hard` nogood is an integrity constraint (no witness atom, no minimize);
         ;; the rest are soft, minimized violations.
         hard-live (filter :hard live)
         soft-live (remove :hard live)
         ;; A cardinality entry's members map to their atoms (sorted, so the weight body
         ;; is content-ordered), then `card-encoding` gives its weight body or drops it as
         ;; vacuous.  Members are contested heads, so all have atoms.
         card-specs (into []
                          (keep (fn [c]
                                  (let [member-atoms (vec (sort (keep atom-of (:members c))))
                                        enc (card-encoding (:op c) (:k c) member-atoms)]
                                    (when-not (= :vacuous enc) (assoc c :enc enc)))))
                          cardinalities)
         hard-cards (filter :hard card-specs)
         soft-cards (remove :hard card-specs)
         ;; Caller priorities become levels by ascending rank, clear of 0 and 1 — a soft
         ;; cardinality breach costs at its own priority alongside the soft nogoods.
         levels    (into {} (map-indexed (fn [i p] [p (+ 2 i)]))
                         (sort (distinct (concat (map :priority soft-live)
                                                 (map #(:priority % 1) soft-cards)))))
         v-atoms   (mapv (fn [ng] [ng (atoms/intern-contradiction! table (descriptor ng))]) soft-live)
         card-v    (mapv (fn [c] [c (atoms/intern-contradiction! table (card-descriptor c))]) soft-cards)
         stmts     (concat
                    ;; believed-or-defeated
                    (map (fn [h] (aspif/choice (atom-of h))) ordered)
                    ;; hard: forbid any model in which the whole (signed) body holds
                    (map (fn [ng] (aspif/constraint
                                   (concat (mapv atom-of (pos ng))
                                           (mapv #(- (atom-of %)) (neg ng)))))
                         hard-live)
                    ;; v :- the whole signed body holds — every `:nogood` member true
                    ;; and every `:neg` member absent, the same body the hard branch
                    ;; forbids.  Positive members alone would emit a `:neg`-only
                    ;; nogood's witness as an unconditional fact: always violated,
                    ;; never steering.
                    (mapcat (fn [[ng v]]
                              [(aspif/rule v (concat (mapv atom-of (pos ng))
                                                     (mapv #(- (atom-of %)) (neg ng))))
                               ;; a minimize / priority soft carries its per-head weight
                               ;; (`:weight`); an ordinary soft costs 1
                               (aspif/minimize (levels (:priority ng)) [[v (:weight ng 1)]])])
                            v-atoms)
                    ;; hard cardinality: ONE weight-body integrity constraint per group —
                    ;; `:infeasible` (a `asp/atLeast` bound no group can meet) is an empty
                    ;; integrity constraint, which excludes every model.
                    (map (fn [{:keys [enc]}]
                           (if (= :infeasible enc)
                             (aspif/constraint [])
                             (aspif/weight-constraint (first enc) (second enc))))
                         hard-cards)
                    ;; soft cardinality: the bound derives a violation atom the minimize
                    ;; path penalizes, so breaching it costs rather than excludes.  An
                    ;; infeasible soft bound is an unconditional violation (always costs).
                    (mapcat (fn [[{:keys [enc priority]} v]]
                              [(if (= :infeasible enc)
                                 (aspif/fact v)
                                 (aspif/weight-rule v (first enc) (second enc)))
                               (aspif/minimize (levels (or priority 1)) [[v 1]])])
                            card-v)
                    ;; keep as much belief as possible: a defeated atom is a false one.
                    ;; Off ⇒ plain satisfaction (no optimization to prove) — see the docstring.
                    (when (and keep-belief? (seq ordered))
                      [(aspif/minimize level-defeat-count
                                       (mapv (fn [h] [(- (atom-of h)) 1]) ordered))])
                    ;; stable tiebreak: cheapest to defeat is the greatest content-key
                    (when (and tiebreak? (seq ordered))
                      [(aspif/minimize level-tiebreak
                                       (map-indexed (fn [i h] [(- (atom-of h)) (- n i)]) ordered))])
                    ;; labels are how the answer set comes back
                    (map (fn [h] (aspif/show (atom-of h) (atoms/label-of-atom table (atom-of h))))
                         ordered)
                    (map (fn [[_ v]] (aspif/show v (atoms/label-of-atom table v))) v-atoms)
                    (map (fn [[_ v]] (aspif/show v (atoms/label-of-atom table v))) card-v))]
     {:aspif       (when (seq stmts) (aspif/render stmts))
      :stmts       stmts
      :table       table
      :by-label    (into {} (map (fn [[ng v]] [(atoms/label-of-atom table v) ng]))
                         (concat v-atoms card-v))
      :assumptions ordered
      :doomed      doomed})))

(defn- answered?
  "Is `result` an answer set — an optimum proven, or a model found with nothing to
  optimize?  `:unsat` is a definite *no model*, which each reader handles on its own
  terms; `:interrupted` and `:unknown` are no result at all (see the ns docstring)."
  [result]
  (contains? #{:optimum :sat} (:status result)))

(defn- unanswered-ex
  "The `:solver-failed` exception for a result that is not an answer, naming the mode
  and the status.  A *value* rather than a throw, because `edge-solver` carries it back
  in `:error` where the imperative readers raise it."
  [mode result]
  (ex-info (str "the ASP backend returned no answer for a " (name mode)
                " solve: " (name (:status result :unknown))
                (when (= :interrupted (:status result))
                  " (the time limit, VAELII_ASP_TIME_LIMIT, or a signal)"))
           {:type :solver-failed :mode mode :status (:status result)}))

(defn- unanswered!
  "Refuse a result that is not an answer, naming the mode and the status."
  [mode result]
  (throw (unanswered-ex mode result)))

(defn- backend-failed-ex
  "`e` — whatever the backend threw — as one `:solver-failed`-shaped exception.

  The backends fail in several currencies: `clingo/chk!` raises `:solver-failed` with
  the `:op` that returned zero, clasp raises `:solver-unavailable` when the binary is
  not there, and a JNA lookup against a missing or wrong-ABI libclingo raises an
  `Error` carrying no data at all.  A caller ranking a failure wants one shape, so the
  original `ex-data` is kept (its `:type` wins, since `:solver-unavailable` says more
  than the generic one) and the throwable rides as the cause."
  [^Throwable e]
  (ex-info (str "the ASP backend failed: " (or (ex-message e) (.getName (class e))))
           (merge {:type :solver-failed} (ex-data e))
           e))

(defn- interpret
  "Read `result`'s answer set back into the `Solver` contract.  `result` has been
  `answered?`-checked by the caller.

  `:violated` is ordered **highest caller priority first, then by content** — the
  `Solver` contract in `solve.clj`.  Taken as they come, the witnesses arrive in
  violation-atom order and the `:doomed` ones ahead of them, which is `translate`'s
  nogood sort: a key of `[members priority hard]` that omits `:sentence`, so two
  constraint rules grounding to the same choice heads at the same priority tie, and
  `sort-by`'s stability then decides the reading by which arrived first.  Sorting here
  rather than widening that key keeps the cost off the grounding path — the nogood sort
  runs over every nogood a program has, this one over the handful that could not be
  satisfied, which in practice is none (see the ns docstring)."
  [{:keys [table by-label assumptions doomed]} result]
  (let [true-labels (set (:atoms result))
        defeated    (into #{} (remove #(true-labels (atoms/label-of-atom table (atoms/atom-of-sentex table %))))
                          assumptions)
        violated    (into (vec doomed)
                          (keep by-label)
                          (sort true-labels))]
    {:defeat defeated
     :violated (nm/sort-by-content-key
                (fn [ng] [(- (long (or (:priority ng) 0))) (:sentence ng)])
                nm/compare-form violated)}))

(defn kept-of
  "The chosen-true assumption handles of one `:label` answer set, read back through
  translation `t`'s atom table — the single-answer-set counterpart to `interpret`'s
  defeat set (kept = assumptions − defeated).  `solve-context`'s `:one` mode reads a
  labeling with it.  An `:unsat` result carries no true labels, so this returns `#{}`
  (nothing kept); an `:interrupted` or `:unknown` one is refused (`:solver-failed`),
  since its empty atom list would read the same way and mean nothing.  A `:best-effort`
  result — the lowest-cost model a cancelled optimization still had in hand — reads like
  an answer: its true labels are a valid labeling, unproven-optimal, which the imperative
  `:one` caller wants over nothing.  The belief path (`edge-solver`) does NOT come here;
  it holds `answered?` to a proven result so a wall clock never moves belief (ns docstring)."
  [{:keys [table assumptions]} result]
  (when-not (or (answered? result) (contains? #{:unsat :best-effort} (:status result)))
    (unanswered! :label result))
  (let [true-labels (set (:atoms result))]
    (into #{} (filter #(true-labels (atoms/label-of-atom table (atoms/atom-of-sentex table %))))
          assumptions)))

(defn- handles-of
  "The assumption handles behind `labels` — a solver's answer set, as label strings."
  [table labels]
  (into #{} (keep #(some->> (atoms/atom-of-label table %)
                            (atoms/sentex-id-of-atom table)))
        labels))

(defn classify-program
  "Classify `program`'s assumptions into `:true` / `:supportable` / `:false` by
  brave/cautious reasoning over its optimal answer sets — in every optimum, in some,
  in none.

  `:fixed` handles are reported `:true`: known-true background is assumed by every
  model, which is what makes it background rather than something the solver decides.
  With no ASP backend every contested assumption is genuinely one of several options,
  so it is reported `:supportable` and nothing is claimed forced or excluded.  An
  enumeration the backend did not finish is refused (`:solver-failed`): a cautious set
  read off a cut-short stream would call forced what was merely not yet ruled out.

  Below `vaelii.core` on purpose — the classification is a property of the encoding and
  the backend, not of any KB — so `settle` can stamp it onto the TMS as belief settles.
  `asp.label` re-exports it for the KB-level callers that predate the move."
  [{:keys [assumptions fixed] :as program}]
  (let [base {:true (set fixed) :supportable #{} :false #{}}]
    (cond
      (empty? assumptions) base
      (not (solver/available?)) (assoc base :supportable (set assumptions))
      :else
      (let [{:keys [aspif table]} (translate program {:tiebreak? false})
            {:keys [cautious brave]} (solver/classify-both aspif)
            _        (doseq [[mode r] [[:classify-true cautious] [:classify-supportable brave]]]
                       (when-not (or (answered? r) (= :unsat (:status r)))
                         (unanswered! mode r)))
            in-every (handles-of table (:atoms cautious))
            in-some  (handles-of table (:atoms brave))]
        {:true        (into (set fixed) (filter in-every) assumptions)
         :supportable (into #{} (filter #(and (in-some %) (not (in-every %)))) assumptions)
         :false       (into #{} (remove in-some) assumptions)}))))

(defn enumerate-optima
  "Every optimal answer set of `program`, each as the **set of its chosen-true
  assumption handles** — the raw material for materializing one labeling context per
  answer set (docs/solving.md).

  Uses the solver's `:all-optima` mode over the **tiebreak-off** encoding, so genuinely
  tied optima come back as distinct witnesses rather than collapsing to one.  A witness's
  atom labels are mapped back through `handles-of`.

  Returns:
  * `[]`        — no assumptions (nothing to decide; the caller makes no labeling);
  * `nil`       — no ASP backend (enumeration needs one; the caller reports that);
  * `[#{h} …]`  — one handle-set per optimum otherwise.

  With assumptions but no nogoods every choice can be kept, so the single optimum keeps
  them all; a `functional`/`disjoint`/`¬` clash is what splits the optima apart.  A
  program whose hard constraints admit no model is `:unsat` and enumerates to `[]`; an
  enumeration the backend did not finish is refused (`:solver-failed`) rather than
  returned as the optima it happened to reach."
  [{:keys [assumptions] :as program}]
  (cond
    (empty? assumptions)      []
    (not (solver/available?)) nil
    :else
    (let [{:keys [table] :as t} (translate program {:tiebreak? false})
          result                (solver/solve t :all-optima)
          {:keys [witnesses]}   (if (or (answered? result) (= :unsat (:status result)))
                                  result
                                  (unanswered! :all-optima result))]
      ;; distinct: two optimal *models* can project to the same set of chosen
      ;; assumptions (they differ only in violation atoms), and those are one labeling
      (into [] (distinct) (map #(handles-of table %) witnesses)))))

(defn- undecided
  "The `Solver` answer for a solve that produced no answer set with a backend present:
  **nothing is decided**.  No defeat, so every contested assumption stands exactly as it
  did; `:violated` still carries the `:doomed` nogoods, which `translate` settled without
  solving anything.  `:error` is the `ExceptionInfo` naming why, for a caller that can act
  on it — `asp.label`'s `solved-labeling` raises it, so an imperative refuses with
  `:solver-failed` instead of committing a labeling nobody computed.

  Deciding nothing rather than degrading is what keeps belief a function of knowledge
  rather than of a wall clock (see the ns docstring), and returning it rather than
  throwing is what keeps a native failure from unwinding an arbitration in progress."
  [t ^Throwable err]
  (trove/log! {:level :error :id ::no-answer-set
               :msg  (str "deciding nothing — " (ex-message err))
               :data (assoc (ex-data err) :assumptions (count (:assumptions t)))})
  {:defeat #{} :violated (vec (:doomed t)) :error err})

(def edge-solver
  "An ASP-backed `solve-types/Solver`.  Install with `(core/set-solver kb edge-solver)`.

  Falls back to `solve/local-solver` when **no** ASP backend is reachable, so this is
  safe to install unconditionally; check `(solver/available?)` if you need to know which
  one will run.  With a backend present it answers from the backend or decides nothing —
  it never mixes the two, and it never throws (see the ns docstring, and `undecided`)."
  (reify solve-types/Solver
    (solve [_ program]
      (let [{:keys [aspif] :as t} (translate program)]
        (cond
          ;; nothing contested — only the structurally hopeless remain
          (nil? aspif)             {:defeat #{} :violated (vec (:doomed t))}
          (not (solver/available?)) (solve-types/solve solve/local-solver program)
          :else
          ;; Only the backend call is guarded, and it is guarded against `Throwable`:
          ;; a native call fails as an `Error` as readily as an exception, and a
          ;; failure there must not unwind an arbitration already in progress.  A
          ;; `settle` that threw out of `resolve-contradictions` would leave a
          ;; half-arbitrated KB — round 1's defeats landed, stale `:conflicts`,
          ;; `settle-finish` never reached and `reset-touched!` never run.  Deciding
          ;; nothing leaves the KB exactly as the round found it.
          (let [result (try (solver/solve t :label)
                            (catch Throwable e {:status :failed :error (backend-failed-ex e)}))]
            (cond
              (answered? result) (interpret t result)
              (:error result) (undecided t (:error result))
              ;; `:unsat` should be unreachable — every contradiction settle sends is
              ;; soft — and is a definite answer wherever it does arrive: the same
              ;; program is `:unsat` in every run, so the stub's reading of it is stable
              ;; and costs the order-independence invariant nothing.
              (= :unsat (:status result))
              (do (trove/log! {:level :warn :id ::unsat
                               :msg  "the ASP program was unsatisfiable; deciding with the local solver"
                               :data {:assumptions (count (:assumptions t))}})
                  (solve-types/solve solve/local-solver program))
              ;; `:interrupted` / `:unknown` (no witness), and `:best-effort` (a witness,
              ;; but one a longer budget might improve): all decide nothing here.  The
              ;; imperative `:one` reader takes a `:best-effort` model — a caller asked for
              ;; a labeling under a deadline — but belief must not turn on a wall clock, so
              ;; this path holds out for a proven answer and otherwise leaves the round be.
              :else (undecided t (unanswered-ex :label result)))))))))
