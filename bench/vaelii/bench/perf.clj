;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.perf
  "The performance regressions this engine has actually shipped, as a gate.

  Every `vaelii.bench.*` harness beside this one *reports* — it prints numbers a person
  reads.  This one *decides*, and it exists because the same defect has now landed twice:
  a per-operation cost that grows with something it should be independent of, turning a
  linear load quadratic.  The defaults phase rescanned every default rule per assert
  (docs/nmtms.md); definitional-clash discovery re-derived every standing pair per
  settle.  Neither broke a test.  Both
  were invisible until somebody sat down and measured, and both had been sitting in
  `main`.

  **What is asserted is a ratio, never a millisecond.**  A wall-clock threshold is either
  loose enough to be useless or tight enough to fail on a loaded laptop, and it has to be
  re-tuned on every machine the project is built on.  What the claims here are actually
  about is *shape*: a cost that should not grow with n is measured at two values of n
  eight to thirty-two times apart, and what is checked is the growth between them.  A
  machine that is twice as slow moves both readings and leaves the ratio alone.

  So a check fails only for the reason it exists: the cost grew with the thing it is
  supposed to be independent of.  Bounds carry real slack — a claim of *flat* passes at
  anything under 2×, which no algorithmic regression respects and no scheduler noise
  reaches.  Two further guards keep it from crying wolf: a check whose baseline is below
  `noise-floor-ns` reports `noise` and is not failed (a ratio between two readings that
  are mostly timer jitter means nothing), and a check that exceeds its bound is measured
  again from scratch, the better of the two runs standing — a GC pause landing in one
  window is not a regression, and a real one survives a second look.

  **A ratio is only as good as its baseline**, and both ways of getting that wrong have
  already happened here.  Warming the JVM proportionally to `n` gave the large size a
  head start and made an n-*independent* check read 0.68x (see `measure`).  And a
  baseline large enough to already carry the cost being measured divides that cost out of
  the answer: `clash-arbitration` at 100 vs 800 could not tell a healthy engine from one
  re-deriving every standing pair, because 100 pairs' worth of the per-pair cost was
  sitting in the denominator.  Both failures read as a *comfortable pass*.  So when
  adding a check, pick the small size to be a size at which the thing being measured has
  barely started.

  **A small baseline is also a cold one, so `--only` and the full run are two different
  measurements — and the difference is large enough to reverse a verdict.**  Where a
  reading is `a + b·n`, the ratio is decided by how big the n-independent `a` is at the
  baseline, and `a` is mostly JIT warmth: by the twentieth check of a run the JVM is far
  warmer than it is on the first.  `negation-arbitration` reads **5.70x under `--only`
  and 6.63x in the full run** on the same tree, and the split is entirely in the
  denominator — its n=100 baseline is 0.347 ms alone against 0.208 in place, while n=800
  barely moves (1.978 against 1.377).  So
  **`--only <name>` cannot clear a failure the full run reported**: it is a quicker way to
  iterate, not a second opinion, and a check that fails in the gate and passes alone has
  said where its baseline is rather than that the gate was wrong.  Judge a check where it
  runs — `retract-merge-scaling` and the two taxonomy-edge checks each carry their own
  numbers for this, and their bounds are read off full runs for it.

  **A bound is read off two measurements, not off one — and never off a guess.**  A
  plausible-looking number nobody measured states its claim in the same shape as every
  measured bound beside it, and no reader downstream can tell the two apart: not a failing
  gate, not a changelog line, not the next person deciding whether a ratio is healthy.  So
  calibrate a new check from **both** ends, on full runs.  Above: the healthy reading, more
  than once, since the spread between runs is what the slack has to cover.  Below: the
  shape the check exists to catch, implemented and measured, because that is the only way
  to know the bound sits under it.  Put the bound between, at about twice the worse healthy
  reading, which is the slack the arbitration checks carry.

  `standing-clash-reading` is the worked example, and it also shows why the guess is worth
  refusing: healthy it reads 85.4x and 80.9x over a floor near 66x, and with the read
  filtering the standing set by cross product it reads 937.8x.  A placeholder of 1000x —
  written to mean \"nobody has measured this\" — **passed** the defective shape.  A bound
  that cannot fail is not a lenient gate, it is an absent one wearing the same syntax.

  **What a ratio cannot see, and it is worth knowing before trusting a green run.**  A
  *constant* per-operation cost added to every write moves both readings by the same
  amount and leaves every ratio here alone — so a new unconditional retrieval on the
  assert path passes this gate untouched.  One has already shipped that way: a third
  argument-constraint declaration read, ~11% on every assert of a declaration-carrying
  predicate, invisible to all of these and found only by timing the absolute cost against
  the previous commit.

  **That class has its own gate now**, and it is a count rather than a duration:
  `test/vaelii/assert_cost_test.clj` pins the exact number of index operations ten fixed
  workloads cost, so an unconditional read added to the assert path fails the suite.
  Restoring the regression above passes every check here and fails six of the ten budgets
  there.  The two are complements — this file holds the *shape* of a cost and that one
  holds the *constant* — and a change to the write path wants both.

  Run: `lein perf [--only <name>] [--tolerance <x>] [--quick]`

    --only       run one check by name (the `:name` below, without the colon)
    --tolerance  multiply every bound by this — 1.5 on a noisy box, 1.0 in anger
    --quick      one attempt over the real pair at a 1.5x-widened bound — a coarse
                 verdict for a pre-commit read, still a verdict

  Exit status is 0 when every check passes, 1 when any fails, which is what makes it
  usable from a hook or a workflow."
  (:require [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.space :as space]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.wiring :as wiring]))

;; ---- measurement --------------------------------------------------------

(def ^:private noise-floor-ns
  "Below this a per-operation reading is mostly timer and scheduler jitter, and the ratio
  of two such readings says nothing.  A check that lands here is reported and skipped
  rather than passed, so a check that becomes too fast to gate says so instead of turning
  into a green light nobody notices has stopped meaning anything."
  20000)                                                    ; 20µs

(defn- fresh-kb
  "An empty KB on its own space, so one check cannot leave state in another's."
  []
  (let [k (v/open-kb {:space 9 :recover? false})]
    (p/clear-records! (:records k))
    (p/clear-index!   (:index k))
    k))

(def ^:private tail-samples
  "How many readings from the end of a run the answer is the mean of — the same count at
  both sizes, so the two answers are averages over windows of equal width rather than
  over a fifth of two runs of different length."
  50)

(defn- tail-mean
  "The mean of the last `tail-samples` readings.  The *last*, because these checks grow a
  KB as they measure it and the question is always what an operation costs once the KB is
  the size the check is about — an average over the whole build would be dominated by the
  cheap early operations and would hide exactly the growth being looked for."
  ^double [xs]
  (let [v (vec xs)
        n (count v)
        k (min n (max 1 tail-samples))]
    (/ (double (reduce + (subvec v (- n k)))) k)))

(defn- measure
  "Per-operation nanoseconds for `f` at size `n`, after warming to `warm`.

  **Both sizes warm to the same amount**, and that is the whole point of the argument.
  Warming proportionally to `n` — a fifth of the run, say — hands the large size a JVM
  that has JIT-compiled the very code being timed while the small size is still climbing
  to it, and the reading comes back *faster at the larger size for no reason but that*.
  It is not a subtle effect: `arg-root-retrieval` does work that is n-independent by
  construction, and it measured 0.68x that way.

  A gate is exactly where that matters, since the bias flatters the large size and a
  ratio bound is a claim about the large size.  A regression would be measured against a
  baseline that had been quietly discounted."
  ^double [f n warm]
  (f warm)
  (f warm)
  (System/gc)
  (tail-mean (f n)))

(defmacro ^:private nanos [& body]
  `(let [t# (System/nanoTime)] ~@body (- (System/nanoTime) t#)))

;; ---- the checks ---------------------------------------------------------
;;
;; Each is `{:name :claim :sizes [small large] :max-ratio :run}`, where `:run` takes a
;; size and returns per-operation nanosecond readings.  `:claim` is what the check is
;; for; it prints beside the verdict, so a failure says which promise broke rather than
;; only which number moved.

(defn- clash-arbitration
  "n individuals each holding two separated types, so the KB carries n standing dilemmas,
  and every assert settles against all of them.

  Runs under `checks/*arbitrate-constraints?*` because that is how a *standing* clash is
  built through `assert` at all — with it off the second membership is refused and the
  pair never exists.  The discovery it gates is the same one the derivation path runs
  unconditionally, so this measures the shipped default too."
  [n]
  (binding [checks/*arbitrate-constraints?* true]
    (let [kb (fresh-kb)]
      (v/assert kb '(disjoint pa_t pb_t) 'CxPerf {:strength :monotonic})
      (doall
       (for [i (range n)
             :let [x (symbol (str "PX" i))]]
         (do (v/assert kb (list 'pa_t x) 'CxPerf {})
             (nanos (v/assert kb (list 'pb_t x) 'CxPerf {}))))))))

(defn- constraint-exposure-shared-arg
  "n facts of a declared-`asymmetric` predicate that all share argument 1, under
  `:refuse`.

  **The one shape the rest of this file cannot see.** Every other check builds its KB
  with `fresh-kb`, which declares no predicate property, so `settle`'s cross-context
  constraint report shuts at its vocabulary gate and never runs — the suite is
  structurally blind to the pass. This declares the property, so the gate opens and each
  assert reaches `clash-vantages`, which reads the argument-1 posting of *both*
  arguments to decide which contexts could see a pair.

  The shared argument is what makes it a claim rather than a formality: `PA`'s posting
  grows by one per assert, so a pass that walks it per assert is O(n) each and O(n²) over
  the load, and the reading tracks the KB rather than the region. One context throughout,
  so no pair is ever visible from anywhere and nothing is reported — this measures the
  cost of *deciding that*, which is the cost every assert on such a KB pays.

  **The posting is predicate-agnostic**, which is what makes the shape general rather
  than contrived: `believed-at-arg1` reads every sentex holding the term at argument 1
  and the functor filter runs after. So the risk is a heavily-used *individual* and not
  only a wide slot — a term at argument 1 of ten thousand facts of other predicates costs
  the same walk. This check drives it with one predicate because that is the shortest
  load that grows the posting; the narrowing it guards (`settle/partner-contexts` reads
  the one posting each declared property could hold a partner in) is what keeps either
  shape flat."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(asymmetric plarger) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'plarger 'PA (symbol (str "PL" i)))
                        'CxPerf {}))))))

(defn- constraint-exposure-context-edge
  "A `genlCx` edge asserted into a KB holding n facts of a declared `functional`
  predicate in the context it newly sees, under `:refuse`.

  The edge is the one trigger the cross-context constraint report reaches *out* of the
  moved region for: visibility moved, so a pair already stored becomes jointly visible
  without either half being relabelled. Reaching out means walking the ancestor set, and an ancestor set
  is unbounded — a context cycle makes it the whole graph — so the walk is lazy and
  spends `*exposure-instance-budget*`.

  **The claim is flatness past the cap, and the cap is bound small here to reach it.**
  Below the cap the walk is proportional to the ancestor set and deliberately so: that is what
  the budget is *for*, and `members-in-ancestors` has cost the disjointness pass the same
  shape since it was written. The cap has to remain a cap — 8x the facts
  behind one edge costs the same once both sides are past it. Measured against the
  default 4096 the reading is the ancestor set and not the cap (5.42x at 250 → 2000), which is
  the check answering a different question rather than a regression.

  Distinct subjects, so nothing in the ancestor set pairs: this measures the reach, not the
  reporting."
  [n]
  (binding [tax/*exposure-instance-budget* 100]
    (let [kb (fresh-kb)]
      (v/assert kb '(functional pbirth) 'CxPerf {:strength :monotonic})
      (v/assert kb '(genlCx CxPSrc CxPerf) 'CxPerf {:strength :monotonic})
      (v/with-deferred-settle kb
        (doseq [i (range n)]
          (v/assert kb (list 'pbirth (symbol (str "PS" i)) i) 'CxPSrc {})))
      (doall
       (for [i (range 60)]
         (nanos (v/assert kb (list 'genlCx (symbol (str "CxPW" i)) 'CxPSrc)
                          'CxPerf {:strength :monotonic})))))))

(defn- unrelated-fact-under-marked-kb-fanout
  "100 facts of a wholly unrelated, unmarked predicate, timed as they arrive in a context
  sitting below n `genlCx` readers -- with a `(functional ...)` mark declared somewhere
  else in the KB, on a predicate this fact's own predicate never touches.

  b3bfb23b bug #2: `derive-functional-equalities` swept `(tax/context-down tax context)`
  on **every** assert the moment any predicate anywhere carried a `functional` or
  `functionalInArg` mark -- gated only by the mark existing in the KB at all, never by
  whether the arriving fact's own predicate had anything to do with it.  Measured up to
  75x slower for an unrelated fact at 6400 context readers.  `special/functional-mark-
  relevant?` is the per-fact pre-gate that skips the closure read entirely once the
  predicate is not reached by any mark; this check is what would have caught its absence
  and is what would catch its guard being loosened back open.

  The mark sits on a predicate the timed facts never mention, and the readers grow below a
  context the marked predicate never stores into: nothing here should make `context-down`
  worth reading at all, so the claim is flatness in the fanout, not merely staying under
  some bound the fanout itself would also satisfy."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(functional pFanoutMarked) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxFanR" i)) 'CxFanBase) 'CxPerf
                  {:strength :monotonic})))
    (doall
     (for [i (range 100)]
       (nanos (v/assert kb (list 'pFanoutUnrelated (symbol (str "PFU" i)) i)
                        'CxFanBase {}))))))

(defn- functional-in-arg-empty-determinant-sweep
  "100 facts arriving under a unary predicate carrying `(functionalInArg P 1)` -- the
  truly-empty determinant shape, where every stored tuple is a candidate partner for
  every other and `settle/partner-contexts` has no argument root to narrow by at all, so
  the partner read is a genuine `subtree-facts` sweep of the predicate's own extent
  (`subtree-facts` reads believed facts KB-wide, with no context filter of its own —
  visibility is decided by the caller, after this walk). Times the assert cost once the
  KB already holds n facts under the mark, under the default `:refuse` policy.

  **Each of the n facts, and each of the 100 timed ones, sits in its own context with no
  `genlCx` edge to anywhere** — mutually blind to every other, including one another.
  An empty-determinant mark makes *any two co-visible* fillers a clash (row 1,
  `functional_in_arg_test.clj`), which a shared context would hit immediately and
  `:refuse` would throw on; isolating every filler is what lets n grow at all without
  the scenario becoming a series of refusals instead of the sweep this measures. It does
  not make the walk this check is about any cheaper: `subtree-facts` still has to read
  KB-wide, unfiltered by visibility, before anything downstream discovers there is
  nothing to convict.

  b3bfb23b bug #3: this sweep shipped **unbudgeted** in fe937b55 -- `subtree-facts` read
  in full per candidate sentex on every settle, contradicting its own docstring's
  'exact and unbudgeted... no enumeration here for a budget to cut short' -- so loading n
  facts under an empty-determinant mark cost O(n) per assert and O(n²) over the load.
  Capped at `*exposure-instance-budget*` here (bound well below `n`, `constraint-
  exposure-context-edge`'s reason): the claim is flatness *past* the cap, not that the
  cap holds the reading down from something worse it would otherwise still grow into."
  [n]
  (binding [tax/*exposure-instance-budget* 100]
    (let [kb (fresh-kb)]
      (v/assert kb '(functionalInArg p_empty_det 1) 'CxPerf {:strength :monotonic})
      (v/with-deferred-settle kb
        (dotimes [i n]
          (v/assert kb (list 'p_empty_det i) (symbol (str "CxPed" i)) {})))
      (doall
       (for [i (range 100)]
         (nanos (v/assert kb (list 'p_empty_det (+ 1000000 i)) (symbol (str "CxPedT" i))
                          {})))))))

(defn- defeasible-load
  "n facts arriving through one defeasible forward rule.  The rule fires per fact and the
  conclusion is placed at `:default`; what must not happen is the whole rule set — or the
  whole KB — being rescanned to decide that."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb (list 'set/defaultRule
                       (rules/rule-sentence ['(pbird ?x)] '(pflies ?x)))
              'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pbird (symbol (str "PB" i))) 'CxPerf {}))))))

(defn- taxonomy-depth
  "n `genl` edges arriving parent-before-child down one chain.  Every edge pays a `wff`
  cycle check, and what keeps that flat is the topological depth potential — a check
  walking the closure instead would be linear in the chain already built."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pt0_t thing) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range 1 (inc n))]
       (nanos (v/assert kb (list 'genl
                                 (symbol (str "pt" i "_t"))
                                 (symbol (str "pt" (dec i) "_t")))
                        'CxPerf {:strength :monotonic}))))))

(defn- taxonomy-belief-flip
  "One `genl` edge defeated and revived over and over, in a taxonomy of n edges.

  Every one of those settles relabels a region of exactly one handle and hands it to
  `tax/refresh-beliefs`, which has to bring the cached closure back in line.  The cost of
  that is the claim: a belief move costs what *moved*, never what the taxonomy holds.
  Two shapes break it and neither breaks a test, because both are merely slow — deciding
  which edges are active by recomputing the believed-supporter set of every edge in the
  relation, and gating that scan by walking every supporter to ask whether any moved.
  Both read as a flip that tracks the vocabulary; the fix is a reverse index off the
  moved handles, and only a load says which one is in.

  The edges are wide rather than deep (every type straight under `thing`) so the build
  stays linear and the reading is about the reconcile, not about `wff`'s cycle check —
  that is `taxonomy-depth` above, and holding both flat takes different machinery."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "pfl" i "_t")) 'thing) 'CxPerf {})))
    (let [edge (list 'not (list 'genl (symbol (str "pfl" (quot n 2) "_t")) 'thing))]
      (doall
       (for [_ (range 120)]
         (nanos (let [h (v/assert kb edge 'CxPerf {:strength :monotonic})]
                  (v/retract! kb h))))))))

(defn- flat-cache-belief-flip
  "One `(disjoint a b)` declaration defeated and revived over and over, in a KB carrying n
  of them.

  The flat-cache twin of `taxonomy-belief-flip`, and the same claim on the other half of
  `tax/refresh-beliefs`: a belief move costs what *moved*, never what the KB declares.
  `:cache-support` is the one map behind all five flat caches, so its population is every
  disjoint pair, predicate property, `inverse` and declared arity in the KB together — a
  reconcile drawn over that is drawn over the vocabulary, and a corpus of OpenCyc's order
  carries tens of thousands.

  The two shapes that break it are the two the closures had, and neither breaks a test
  because both are merely slow: deciding which entries are active by evaluating belief for
  every entry in the map, and gating that scan by walking every supporter to ask whether
  any moved.  The **gate** is the one this check is really about — most settles move no
  declaration at all, so a miss that walks the whole supporter set is a cost every settle
  pays to learn it had nothing to do.  Both read as a flip that tracks the vocabulary; the
  fix is a reverse index off the moved handles, and only a load says which one is in.

  Each pair is over types of its own, so nothing is a subtype of anything and no instance
  is asserted: the reading is about the reconcile, not about `disjoint?`'s walk over two
  `genl` closures."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'disjoint (symbol (str "pfd" i "a_t")) (symbol (str "pfd" i "b_t")))
                  'CxPerf {})))
    (let [k    (quot n 2)
          decl (list 'not (list 'disjoint (symbol (str "pfd" k "a_t")) (symbol (str "pfd" k "b_t"))))]
      (doall
       (for [_ (range 120)]
         (nanos (let [h (v/assert kb decl 'CxPerf {:strength :monotonic})]
                  (v/retract! kb h))))))))

(defn- arg-root-retrieval
  "A pattern pinning an argument that sits *after* a variable — `(pRelOf ?x Tk)`, which no
  trie prefix reaches.  The argument roots answer it by one set intersection; without them
  the whole predicate extent is scanned, so the cost would track n."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pRelOf (symbol (str "PI" i)) (symbol (str "PT" i)))
                  'CxPerf {:strength :monotonic})))
    ;; a hundred matches per reading: one is a few microseconds whatever n is, which is
    ;; the very result being gated — and a ratio between two readings that small is
    ;; timer jitter.  Batching moves the reading above the floor without changing what
    ;; it measures.
    (let [goal (list 'pRelOf '?x (symbol (str "PT" (quot n 2))))]
      (doall (for [_ (range 40)]
               (nanos (dotimes [_ 100] (doall (res/match-pattern kb goal 'CxPerf)))))))))

(def ^:private separated-types
  "Types under each side of the one declaration in `disjoint-enumeration` — the part of
  that KB the goal is actually about, held fixed while the vocabulary around it grows."
  20)

(defn- disjoint-enumeration
  "An open `(disjoint T ?t)` goal over a KB of n types in which **one** declaration
  separates two twenty-type subtrees.  The answer is twenty-one types at every n; what
  n moves is the vocabulary the goal is not about.

  A `(disjoint x y)` separates two subtrees and convicts `specs(x) × specs(y)`, and
  nothing reaches a candidate any other way — so an answer costs the answer's own size,
  and the type count is not in it.  The shape this holds flat is the other enumeration:
  one `disjoint?` per type in the KB, which on an imported ontology (docs/kbs.md) is a
  scan of 132,391 types to produce twenty-one.

  Ten asks per reading, since one is a fraction of a millisecond at any n — which is
  the result being gated, and a ratio between two readings that small is jitter."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pdj_left thing)  'CxPerf {:strength :monotonic})
    (v/assert kb '(genl pdj_right thing) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range separated-types)]
        (v/assert kb (list 'genl (symbol (str "pdj_l" i)) 'pdj_left)
                  'CxPerf {:strength :monotonic})
        (v/assert kb (list 'genl (symbol (str "pdj_r" i)) 'pdj_right)
                  'CxPerf {:strength :monotonic}))
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "pdj_o" i "_t")) 'thing)
                  'CxPerf {:strength :monotonic})))
    (v/assert kb '(disjoint pdj_left pdj_right) 'CxPerf {:strength :monotonic})
    (doall (for [_ (range 60)]
             (nanos (dotimes [_ 10] (count (v/ask kb '(disjoint pdj_l0 ?t) 'CxPerf))))))))

(defn- disjoint-clique-membership
  "A type membership arriving under a predicate that sits in an n-way sibling-disjoint
  clique — `(sibling_disjoint SibRoot)` with n children `genl` SibRoot, so those n
  children are mutually disjoint — where the arriving term already holds one *benign* type
  the clique does not separate.  Every such assert builds the arriving type's separation
  frame (whose sibling arm consults `specs(SibRoot)`) and tests the benign membership
  against it.

  The claim is **flatness in the clique size**.  `separation-frame` reads `specs(SibRoot)`
  once and closes over the set, and the candidate test is a `contains?` against it rather
  than a scan of the n members, so a member test costs the same against a thousand-way
  clique as against a ten-way one.  This is the assert-path twin of `disjoint-enumeration`
  (the query side) and `flat-cache-belief-flip` (the reconcile side): the shape it holds
  flat is a check that walks the whole clique per candidate, or rebuilds the frame per
  candidate over an unmemoized `specs` walk — either turns this O(clique) per assert and
  O(clique·asserts) over the load.  `checks/cascade-clash` and `wff/disjoint-problems`
  both build the frame once through `disjointness-test` for this reason.

  Distinct arriving terms, each pre-holding the same benign type, so nothing here is a
  clash and no term accumulates memberships: the reading is the cost of *deciding* a
  benign membership is admissible under a large clique, which is what every such assert
  on such a KB pays.

  Measured flat: 0.84-0.95x at 500 → 4000 clique members over three runs (the sub-1.0
  readings are the large size's JIT-warming bias `measure` documents, not a speedup).  The
  bound is the standard 2.0 the flat claims carry — about twice the worst healthy reading."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pdcm_benign thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(sibling_disjoint pdcm_root) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "pdcm_s" i)) 'pdcm_root)
                  'CxPerf {:strength :monotonic})))
    (doall
     (for [i (range n)
           :let [x (symbol (str "PDCM" i))]]
       (do (v/assert kb (list 'pdcm_benign x) 'CxPerf {:strength :monotonic})
           (nanos (v/assert kb (list 'pdcm_s0 x) 'CxPerf {:strength :monotonic})))))))

(defn- disjoint-metatype-membership
  "The metatype twin of `disjoint-clique-membership`: a membership arriving under a type
  that is a member of an n-member `disjoint_metatype`, the term already holding a benign
  type the metatype does not separate.  The metatype arm of `disjointness-test` scans the
  member roster (`filterv … ms`) per candidate rather than reading `contains?` off a
  memoized closure the way the sibling arm does — the members are a stored set with no
  closure to memoize — so this is the arm whose per-candidate cost tracks the member count.

  The claim is **at most linear in the member count**, not flat and not quadratic: one
  scan of the n members per candidate is the shape the arm is written to have (the comment
  at the arm says a metatype has a handful where a closure has a chain's worth), so the
  reading is expected to track n once the scan dominates.  The bound guards the step to
  quadratic — rebuilding the frame per candidate over an unmemoized member filter, or a
  member-vis probe that itself walks — which would make an assert O(members²).

  Measured linear: 4.92-5.26x at 500 -> 4000 members (the `a + b·n` shape — a ~0.07ms
  n-independent floor plus ~0.22µs a member — dilutes an 8x size step to ~5x at this
  baseline, and approaches 8x as the member scan dominates).  Bound 12.0: above the ~8x a
  larger baseline would read and well under the ~64x a per-member-quadratic regression
  would cost, the `membership-under-depth` precedent for a grows-with claim."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pdmt_benign thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(disjoint_metatype pdmt_meta) 'CxPerf {:strength :monotonic})
    (v/assert kb '(unary_predicate pdmt_m0) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pdmt_meta (symbol (str "pdmt_m" i))) 'CxPerf {:strength :monotonic})))
    (doall
     (for [i (range n)
           :let [x (symbol (str "PDMT" i))]]
       (do (v/assert kb (list 'pdmt_benign x) 'CxPerf {:strength :monotonic})
           (nanos (v/assert kb (list 'pdmt_m0 x) 'CxPerf {:strength :monotonic})))))))

(defn- closure-membership
  "`(pBefore Head Tail)` over an n-long chain under `(transitive pBefore)`, asked after the
  chain's closure has been asked once.

  The two questions are different and the gate is on the second.  Computing the closure is
  the length of the chain and always will be; **asking whether one pair is in a closure
  already computed is a set membership**, so it is flat in the chain — the pair asked is
  head-to-tail, the far end, which is the reading a walk cannot hold flat because a walk
  is exactly the distance between them.

  The open ask runs once, outside the timed loop: it is what fills the answer cache, and
  timing it would gate the closure's own cost instead of the membership's.  `dorun`, not a
  bare call — `ask` is lazy all the way down, so an unrealized one computes no closure and
  fills nothing.  Two hundred asks per reading, since one is microseconds at either size."
  [n]
  (let [kb (fresh-kb)
        nd #(symbol (str "PBefore" % "Individual"))]
    (v/assert kb '(transitive pBefore) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range 1 n)]
        (v/assert kb (list 'pBefore (nd (dec i)) (nd i)) 'CxPerf {:strength :monotonic})))
    (dorun (v/ask kb (list 'pBefore (nd 0) '?y) 'CxPerf))
    (let [goal (list 'pBefore (nd 0) (nd (dec n)))]
      (doall (for [_ (range 60)]
               (nanos (dotimes [_ 200] (v/ask? kb goal 'CxPerf))))))))

(defn- membership-check
  "A type membership arriving into a KB that already holds n of them, each about a
  *different* individual.  The disjointness arm reads the term's own argument-1 root
  rather than everything that mentions it, so the cost is the arriving term's own
  memberships and nothing about how many other terms have some.

  Deliberately not *one* term accumulating n types: the check must compare a new
  membership against the ones that term already holds, so that shape is linear by
  definition and gating it would be gating a claim nobody makes."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pm_a_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(genl pm_b_t thing) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)
           :let [x (symbol (str "PM" i))]]
       (do (v/assert kb (list 'pm_a_t x) 'CxPerf {:strength :monotonic})
           (nanos (v/assert kb (list 'pm_b_t x) 'CxPerf {:strength :monotonic})))))))

(defn- membership-under-depth
  "A type membership arriving under a predicate that sits `n` deep in a `genl` chain,
  none of the chain declaring an arity.

  The axis none of the other checks vary.  `membership-check` above holds the hierarchy
  flat and grows how many memberships the KB already holds; `taxonomy-depth` grows the
  chain but measures asserting the *edges* rather than a fact under them.  So the cost of
  the arity descension's per-super membership read — the one thing on this path that
  grows with the depth above the predicate being asserted — was invisible to all thirty
  checks, and shipped once for that reason.

  The claim is deliberately not `flat`.  `inherited-arity` asks the `variable_arity`
  release of every super-predicate; that question is a retrieval the arity table cannot
  answer, and no roster can gate it while a `variable_arity` reached through a `genl` edge
  between collections releases exactly as a directly asserted one does.  So the bound is
  a record of the shape today rather than a target, in the sense `assert-cost-test`'s
  preamble means it: a change that makes the descension flat in the depth drops this to
  about 1.0 and re-pins as an improvement, and a change that makes it worse fails."
  [n]
  (let [kb (fresh-kb)
        t  (fn [i] (symbol (str "pmud_t" i)))]
    (v/assert kb (list 'genl (t n) 'thing) 'CxPerf {:strength :monotonic})
    (doseq [i (range n)]
      (v/assert kb (list 'genl (t i) (t (inc i))) 'CxPerf {:strength :monotonic}))
    ;; warm, so the reading is the steady-state assert rather than the first one's caches
    (dotimes [i 50] (v/assert kb (list (t 0) (symbol (str "PMUDW" i))) 'CxPerf {}))
    (doall
     (for [i (range 200)]
       (nanos (v/assert kb (list (t 0) (symbol (str "PMUD" i))) 'CxPerf {}))))))

(defn- negation-arbitration
  "n **independent** P/¬P dilemmas — a fresh predicate and a fresh individual apiece, so
  no pair shares a body, a term or a context of concern with any other — and every assert
  settles against all of them.

  The twin of `clash-arbitration`, for the other nogood source.  A settle republishes the
  whole standing set either way, so the bound is Ω(standing) here too and the claim is the
  same one: the per-pair term must stay **bookkeeping** — a set union and a belief read —
  rather than re-deriving each standing pair from the store.  Re-derivation means two
  belief-filtered `query` calls and a cross product per opposed body per settle *round*,
  which is what makes a load of N dilemmas Θ(N²).

  Nothing here is a *definitional* clash, so `checks/*arbitrate-constraints?*` is
  irrelevant and the pairs are pure `negation-nogoods` business."
  [n]
  (let [kb (fresh-kb)]
    (doall
     (for [i (range n)
           :let [pr (symbol (str "pneg" i))
                 x  (symbol (str "PN" i))]]
       (do (v/assert kb (list pr x) 'CxPerf {})
           (nanos (v/assert kb (list 'not (list pr x)) 'CxPerf {})))))))

(defn- negation-load
  "n negative facts whose bodies are stored in ONE polarity only — the negation-heavy load
  that carries no contradiction at all.

  The complement of `negation-arbitration`, and it guards the other half of the same
  namespace.  A settle that enumerated every stored negated body looking for a believed
  positive twin would be Θ(N²) here even though not one of these bodies has a twin; the
  `:opposed` coincidence set holds exactly the doubly-stored bodies, so this pays one
  emptiness read.  The two checks fail for opposite reasons — this one if the
  *discovery* stops being incremental, its twin if the *pairing* does — and a fix aimed at
  either can regress the other, which is why both are here."
  [n]
  (let [kb (fresh-kb)]
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'not (list (symbol (str "pnl" i)) 'PNA))
                        'CxPerf {}))))))

(defn- compound-probe
  "`find-sentexes` on a ground **compound** — `(pcmp PI0 PTHot)`, a stored fact of a corpus
  of n over a fixed vocabulary, one of whose atoms (`PTHot`) every one of those n mentions.

  A compound earns no key of its own at the default `sx/*min-indexed-depth*` — the key
  that makes the token dictionary fact-scaled rather than vocabulary-scaled — so this read
  narrows on the atoms' postings and verifies each candidate against its record.  That is
  only a sound exchange if the narrowing is a property of the *rare* atom: `PI0` names one
  fact, so the answer is one fact, and the hot atom must not put the extent back into the
  cost.  Which is the claim `intersect-selectivity` makes about the roots, asked here of
  the read that now rests on it.

  A hundred probes per reading, since one is a few microseconds at any n and a ratio
  between two readings that small is timer jitter."
  [n]
  (let [kb (fresh-kb)]
    (v/bulk-assert-facts!
     kb (for [i (range n)] (list 'pcmp (symbol (str "PI" i)) 'PTHot)) 'CxPerf)
    (let [c (list 'pcmp 'PI0 'PTHot)]
      (doall (for [_ (range 200)]
               (nanos (dotimes [_ 100] (doall (v/find-sentexes kb c)))))))))

(def ^:private retract-victims
  "Retractions timed per run.  **The same count at both sizes**, and more than
  `tail-samples`, so each answer is the mean of the last fifty and the two windows have
  the same width.  Each victim is a separate fact, since a handle can only be retracted
  once — where an assert check re-runs one operation, this one needs a supply of them."
  60)

(defn- retract-nat-scaling
  "One `retract!` of a fact that names no NAT, on a KB carrying n **live** reified NATs.

  Every other check here times an assert or a query; this is the one that times a
  **retraction**, and the class it covers is the teardown sweep.  A retraction runs the
  reified-NAT orphan collection, because a constant whose last use has just gone would
  otherwise leave its `termOfUnit` map and materialized types dangling a raw `nat/`
  symbol (docs/nat.md).  What the sweep may cost is what the retraction *reached*; what
  it may not cost is what the KB *holds*, which is the claim measured here.

  The n NATs are all **live**: each is named by its own `(pNatUse PNUi K)` fact and no
  timed retraction touches one, so the sweep finds nothing at either size and every
  reading is the same removal doing the same work.  A population of *orphans* would
  measure the opposite thing — real removals the sweep is right to be doing, growing with
  n for a reason no fix should take away — and would read as this defect while being
  correct behaviour.

  The victims are plain binary facts of fresh individuals: nothing they name is reified,
  so nothing they leave behind can be orphaned and the population is the same at the last
  reading as at the first."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(reifiable_function PNatFn) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pNatUse (symbol (str "PNU" i))
                           (list 'PNatFn (symbol (str "PNA" i))))
                  'CxPerf {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pRetVictim (symbol (str "PRV" i)) 'PRVal)
                                    'CxPerf {}))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))

;; ---- store-level checks --------------------------------------------------
;;
;; The eight checks above drive `vaelii.core`, because the claims they defend are about
;; what an *assert* or a *query* costs.  The four below sit at the storage protocols
;; instead: each defends an operation a backend advertises as constant-time and that an
;; engine path therefore calls per firing or per query plan.  A wrong answer there is not
;; a wrong answer at all — the differential oracles prove every backend returns the same
;; sets — so nothing but a measurement can catch it, and the flat-map backend the rest of
;; the suite runs on is the one backend where each of them happens to be constant.

(def ^:private writes-per-reading
  "Index writes batched into one timed reading.  A single write is a microsecond or two —
  below `noise-floor-ns`, where a ratio is jitter — so the reading is a fixed batch of
  them, **the same batch at both sizes**, exactly as `arg-root-retrieval` times a hundred
  matches rather than one.  Small enough that the smaller size still yields more readings
  than `tail-samples` takes, or the two answers would be averages over windows of
  different width."
  50)

(def ^:private reads-per-reading
  "The same, for a root read — and an order of magnitude more of them, because a read that
  has stopped being linear is *fast*: both checks below landed at or under 20µs a batch of
  50 once fixed, which is `noise-floor-ns`, and a check that drops below the floor stops
  gating and says so rather than going quietly green.  A batch this size keeps the fixed
  reading well clear of the floor, so the check still fails if the cost comes back."
  500)

(defn- columnar-fanout
  "n sentexes on ONE predicate with n distinct first arguments, so the columnar trie's
  level-2 node ends up holding n child edges.

  What is being gated is the node's own insert, not the trie's depth: every other level
  here is width 1 (one functor, one context per argument), so the only thing that grows
  between the two sizes is the fan-out of the single node every insert passes through.  A
  per-node child structure whose insert is proportional to the children already there
  makes a load of one broad predicate — `(isa X T)`, `(genl S T)`, any hot relation in a
  real ontology — quadratic in its own extent.

  The columnar index specifically, because it is the backend built *for* 100M
  (docs/density.md): the flat-map and dense backends key a child edge in a hash and are
  flat here by construction."
  [n]
  (let [st  (columnar/columnar-index-store {:space [::fanout]})
        sxs (mapv (fn [i] (sx/sentex (list 'pfan (symbol (str "PF" i))) 'CxPerf {}))
                  (range n))]
    (p/clear-index! st)
    (doall
     (for [batch (partition-all writes-per-reading (range n))]
       (nanos (doseq [i batch] (p/index-sentex st (nth sxs i) i)))))))

(defn- exception-roster-gate
  "`exception-rule?` against a roster of n rules — the gate `chain/rule-view-of` takes
  once per candidate rule per new datum, before it will fetch a rule's exceptions.

  `p/exception-rule?` is specified as an O(1) membership test, and the firing path is
  written on the assumption: an ordinary rule is supposed to pay one set-membership read
  and nothing else.  A backend that answers it by *materializing* the roster instead turns
  every forward firing into a product of two KB-sized quantities — the rules a fact
  triggers times the rules that carry an exception.

  Measured on the `:dense` index, where the roster is a handle-set family (an
  `IntPostings`), since that is the representation the flat-map backend's plain set does
  not have and so the one where the distinction between *reading* a set and *building* one
  can be seen at all."
  [n]
  (let [st (dense/dense-index-store {:space [::roster]})]
    (p/clear-index! st)
    (doseq [i (range n)] (p/index-exception st i ['pexc]))
    (doall
     (for [r (range 200)]
       (nanos (dotimes [i reads-per-reading]
                (p/exception-rule? st (mod (+ i r) n))))))))

(defn- overlay-selectivity
  "`count-with-functor` on a fork, for a functor root of n handles the fork has never
  touched — the cardinality read `plan/order` costs every conjunct off and
  `provers/est-bindings` reads per goal.

  A fork inherits nearly all of its content: the whole point is that N processes share one
  base and each writes a little (docs/overlay.md).  So the overwhelmingly common shape of
  this read is the one measured here — a key with no overlay entry, no recorded removal
  and no tombstone, whose answer is exactly the base's own count.  Merging in order to
  count makes every query plan proportional to the extents it is costing.

  Over a `:dense` base, because that is where the base's `kv-members` builds a set rather
  than handing one back: an overlay that merges before counting is flat over a flat-map
  base and linear over that one, and only the second says whether the *code* merges."
  [n]
  (let [base (dense/dense-kv-backend {:space [::ovbase]})]
    (p/kv-clear! base)
    (doseq [i (range n)] (p/kv-add-to-set base [:functor-root 'povl] i))
    (let [own (mem/memory-kv-backend {:space [::ovfork]})
          _   (p/kv-clear! own)
          st  (kv/->KvIndexStore (okv/overlay-kv own (frozen/frozen-kv base)))]
      (doall
       (for [_ (range 200)]
         (nanos (dotimes [_ reads-per-reading] (p/count-with-functor st 'povl))))))))

(defn- intersect-selectivity
  "`sentexes-with-args` for a pattern pinning a **rare** argument beside a **hot** one
  on the same predicate — `(pint ?x PIA PIB)` with four handles at position 1 against n
  at position 2 — which is one `kv-intersect` over the two scoped argument roots,
  `[:argument-root pint 1 PIA]` ∩ `[:argument-root pint 2 PIB]`.  A single bound
  argument intersects nothing (the scoped root is one hash lookup), so two bound
  positions are the structure that exercises `kv-intersect`.

  The answer is a property of the rare side: four entries, each tested against the hot
  posting.  A backend that materializes both roots into Clojure sets before intersecting
  pays for the hot one instead, so the query becomes proportional to the extent it is
  narrowing *out of* — which is the cost the argument roots exist to avoid, and turning
  them on would buy nothing if the intersection put it back.  `arg-root-retrieval` keeps
  the same shape out of the trie path; this keeps it out of the roots.

  Over the `:dense` index, because that is where a posting has a representation to narrow
  in.  The flat-map backend hands its stored set straight back and is flat here by
  construction, so it cannot see the difference."
  [n]
  (let [b (dense/dense-kv-backend {:space [::inter]})]
    (p/kv-clear! b)
    (doseq [i (range n)] (p/kv-add-to-set b [:argument-root 'pint 2 'PIB] i))
    (doseq [i (range 4)] (p/kv-add-to-set b [:argument-root 'pint 1 'PIA] (* 7 i)))
    (let [st (kv/->KvIndexStore b)]
      (doall
       (for [_ (range 200)]
         (nanos (dotimes [_ reads-per-reading]
                  (p/sentexes-with-args st 'pint [[1 'PIA] [2 'PIB]]))))))))

(defn- plan-scaling
  "Planning one fixed four-literal conjunction against a KB of `n` facts per relation.

  The conjunction never changes, so anything that grows here is the planner reading
  something proportional to the *data* rather than to the question — and a plan is
  computed per rule expansion, per node in the node engine, and per `prove` call, so a
  planner that scales with the KB scales with it on every one of those.

  The reading this exists to hold flat is the trie's distinct-value count, which the
  cost model divides by (`plan/est-rows`, `plan/est-matches`) and therefore asks once
  per literal per plan.  `count-children` answers it off a set's cardinality or an edge
  span; `(count (children …))` would answer the same number by materializing the child
  set, which is O(how many distinct values sit at that position) and one vector per
  call.  At 32x the facts that reads 30x the planning cost, and the conjunction being
  planned is identical at both sizes — so this ratio sees it and nothing else here
  does.

  The relations are 1:1 chains beside a small disconnected one, which is the structure that
  makes the planner do all of its work: three blocks to rank, a cartesian factor to
  place, and a distinct-value count read at every literal."
  [n]
  (let [kb (fresh-kb)
        q  '[(perfPlanLoose ?u ?v) (perfPlanA ?a ?b) (perfPlanB ?b ?c) (perfPlanC ?c ?d)]]
    (v/assert-many kb
                   (concat (for [i (range n)]
                             (list 'perfPlanA (symbol (str "PpX" i)) (symbol (str "PpY" i))))
                           (for [i (range n)]
                             (list 'perfPlanB (symbol (str "PpY" i)) (symbol (str "PpZ" i))))
                           (for [i (range n)]
                             (list 'perfPlanC (symbol (str "PpZ" i)) (symbol (str "PpW" i))))
                           (for [i (range 20)]
                             (list 'perfPlanLoose (symbol (str "PpU" i)) (symbol (str "PpV" i)))))
                   'CxUniverse {:chain? false})
    (doall
     (for [_ (range 200)]
       (nanos (dotimes [_ 20] (plan/order kb q 'CxUniverse {})))))))

(defn- arity-reach-trigger
  "n **conforming** facts of a predicate whose arity was declared before any of them.

  `settle/report-arity-reach!` sweeps the **spec subtree** of every predicate a binding
  names, and the only thing that keeps that affordable is *what triggers it*: a binding
  entering the moved region, never a fact.  Four sentences are bindings — `(arity P n)`,
  the predicate-type membership that spells the same thing, a `genl` edge that inherits one
  through, and a `genlCx` edge that lets a vantage see either — and a fact of a declared
  predicate is none of them.  So an ordinary fact arriving must cost the same at 2,000 as
  at 250, and mis-gating the pass to run on every settle — the easy mistake, since every
  other pass in `settle-finish` does — turns a linear load quadratic here and in no test.

  Conforming on purpose.  A load of *violating* facts would sweep once, at the
  declaration, and then measure the ordinary assert path anyway; what this has to separate
  is a pass that runs per fact from one that runs per declaration, and a conforming extent
  makes any sweep at all visible as growth rather than hiding inside a report."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(arity pReach 2) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pReach (symbol (str "PR" i)) 'PRval) 'CxPerf {}))))))

(defn- feed-listener-scaling
  "n asserts on a KB with two change-feed listeners attached — one plain, one a standing
  query the arriving fact answers.

  The feed's whole cost argument is that an event is proportional to the **region a
  settle relabelled** and never to what is stored.  Two plausible implementations break
  that and neither breaks a test: snapshotting the believed set and diffing it is O(KB)
  per write, and answering a standing query by re-running its goal makes every mutation
  cost a query per listener.  Both read as a per-assert cost that grows with the load,
  which is what this separates from a per-region one.

  The listeners discard their events on purpose — what is being measured is the engine's
  cost of *producing* one, not a consumer's cost of handling it.  A standing query is
  included because it is the structure that would re-run something: it has to filter the
  region rather than ask the KB again, and only a load says which it did."
  [n]
  (let [kb (fresh-kb)]
    (v/watch kb (fn [_] nil))
    (v/watch kb '(pFeed ?x ?y) 'CxPerf (fn [_] nil))
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pFeed (symbol (str "PF" i)) 'PFval) 'CxPerf {}))))))

(defn- quality-report-scaling
  "`kb-quality` over n stored facts, where n grows 8x and the **vocabulary** grows 2.8x:
  the facts pair √n individuals against √n others, so the sentex count is the square of
  the term roster.

  That shape is what separates the two implementations of the report.  Every reading it
  takes is off the vocabulary — an extent per predicate, the rule postings per predicate,
  the genl closure per type — and the one that is *easy* to write instead scans the record
  store to find the rules, which reads as O(sentexes) and grows with the square.  A
  quality report that costs what the KB costs is one nobody runs on the KB that needs it,
  and nothing but a load says which was written."
  [n]
  (let [kb   (fresh-kb)
        side (long (Math/ceil (Math/sqrt (double n))))]
    (v/assert kb '(genl qual_thing thing) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range side), j (range side)]
        (v/assert kb (list 'pQual (symbol (str "QA" i)) (symbol (str "QB" j)))
                  'CxPerf {})))
    (doall (for [_ (range 60)] (nanos (v/kb-quality kb))))))

(def ^:private census-supers
  "Predicates stacked above the one predicate `quality-declaration-census` declares
  against — the hierarchy held **fixed** while the declaration count moves, so the census's
  per-declaration arity read is a real walk at both sizes and the same walk at both."
  8)

(defn- quality-declaration-census
  "`kb-quality` over n argument constraints on **one** predicate, under a fixed hierarchy.

  The census takes seven readings and `quality-report-scaling` above drives four of them:
  its KB declares no `arg`, `genlArg` or `interArg`, so `quality/stranded-declarations`
  walks an empty list at 4,000 sentexes and at 32,000 alike, and it stores no rule, so the
  two rule-hygiene readings pair an empty set.  This is the workload that drives the
  declaration census, and it is built the other way round from that one on purpose — the
  vocabulary is one predicate, one type and `census-supers` supers at **both** sizes, so
  every other reading the census takes is fixed and the whole of the growth here is the
  declaration walk.

  Each declaration is a distinct **position** on the same predicate, which is what holds
  the vocabulary still while the count moves.  Nothing declares a length, and that is the
  expensive case rather than a degenerate one: `checks/declared-arity` answers off a map
  for a predicate carrying a length of its own and off a walk of its super-predicates for
  one that does not, so a KB that has stated no arity is the KB where every declaration
  pays the walk.  The cost is `O(declarations × super-predicates)` and this check pins the
  first factor.

  Ω(declarations) is the floor — the census reads each one, and reading them is the work —
  so the claim is linear.  What the bound separates is one reading per declaration from one
  reading per declaration *per declaration*: an arity re-derived off the index per question
  rather than off the taxonomy's table walks the argument-1 posting these n declarations
  are exactly what fills."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl qdc_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb (list 'genl (symbol (str "qdcB" census-supers)) 'qdcTop)
              'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (v/assert kb '(genl qdcPred qdcB0) 'CxPerf {:strength :monotonic})
      (doseq [i (range census-supers)]
        (v/assert kb (list 'genl (symbol (str "qdcB" i)) (symbol (str "qdcB" (inc i))))
                  'CxPerf {:strength :monotonic}))
      (doseq [i (range 1 (inc n))]
        (v/assert kb (list 'arg 'qdcPred i 'qdc_t) 'CxPerf {:strength :monotonic})))
    (doall (for [_ (range 60)] (nanos (v/kb-quality kb))))))

(def ^:private depth-declarations
  "Argument constraints standing while `quality-declaration-depth` moves the hierarchy —
  its own knob rather than the size, because it is the factor that check holds fixed.  Big
  enough that the declaration walk is the reading: at n=256 the same KB stripped of these
  costs a tenth of what it costs with them, so nine parts in ten of what the ratio sees is
  the walk and one is the vocabulary the chain adds."
  256)

(defn- quality-declaration-depth
  "`kb-quality` over `depth-declarations` argument constraints whose predicate sits under a
  chain of n super-predicates.

  The second factor of the same bound, and the axis the check above holds still.  A
  declaration's arity read is `checks/declared-arity`, which walks the supers of a
  predicate that declares no length of its own and asks each for its own — so the census
  costs `O(declarations × super-predicates)` and neither factor alone says the product is
  right.  Nothing in the chain declares a length, so every declaration walks to the end of
  it.

  Ω(depth) is the floor, so the claim is linear here too, and it is a claim about the
  *shape* rather than about the constant: the membership read behind the walk is memoized
  for the life of one census, so a super met by the first declaration costs the other 255
  a map hit.  A change that throws that memo away pays a retrieval per super per
  declaration and this ratio cannot see it — that is `assert-cost-test`'s subject, on the
  entry point's own copy of the same walk.  What the bound separates is a walk of the supers from
  a walk of each super's own ancestry."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl qdd_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb (list 'genl (symbol (str "qddB" n)) 'qddTop) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (v/assert kb '(genl qddPred qddB0) 'CxPerf {:strength :monotonic})
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "qddB" i)) (symbol (str "qddB" (inc i))))
                  'CxPerf {:strength :monotonic}))
      (doseq [i (range 1 (inc depth-declarations))]
        (v/assert kb (list 'arg 'qddPred i 'qdd_t) 'CxPerf {:strength :monotonic})))
    (doall (for [_ (range 20)] (nanos (v/kb-quality kb))))))

(defn- pctx [prefix i] (symbol (str "Cx" prefix i)))

(defn- retract-context-cycle-scaling
  "One `retract!` of a `genlCx` edge **inside a two-context cycle**, on a KB whose
  context graph holds n unrelated contexts beside it.

  Two contexts that see each other sit in a strongly connected component, and a deletion
  inside one can split it.  A split is the only edit that invalidates the component map,
  and the map is what `sees?` reads for its O(1) same-component answer, so it may not be
  left stale.  What the repair may cost is that component; what it may not cost is the
  graph around it, which is the claim measured here.

  A cycle-closing `genlCx` edge is refused at assert, like a `genl` one, so a live cycle
  reaches the taxonomy only through a belief race (or a recovered store).  Each cycle
  below forms the belief-race way (docs/taxonomy.md): `PcB → PcA` stands, a monotonic
  negation defeats it, `PcA → PcB` asserts while no active cycle stands, and retracting the
  defeater revives `PcB → PcA`, so the two contexts see each other.  No other check in this
  file builds a context cycle at all, which is exactly how a whole-relation repair per
  deleted cycle edge stayed invisible.

  One cycle per victim, because a handle can only be retracted once and a broken cycle
  cannot be broken again.  The unrelated contexts are the population held fixed: none of
  them is in any cycle, none is named by any retraction, and the count is the same at the
  last reading as at the first."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (pctx "PcBg" i) 'CxPcTop) 'CxUniverse {}))
      (doseq [i (range retract-victims)]
        (v/assert kb (list 'genlCx (pctx "PcA" i) 'CxPcTop) 'CxUniverse {})
        (v/assert kb (list 'genlCx (pctx "PcB" i) (pctx "PcA" i)) 'CxUniverse {})))
    ;; the closing edges last and outside the batch: each settles, so the component map is
    ;; built and the relation is ranked before a single reading is taken.  `wff` refuses a
    ;; cycle-closing edge, so PcA → PcB closes each cycle through a belief race — defeat the
    ;; standing PcB → PcA, assert PcA → PcB while no active cycle stands, revive PcB → PcA —
    ;; and the asserted PcA → PcB closing edge is the timed victim.
    (let [victims (mapv (fn [i]
                          (let [back-edge (list 'genlCx (pctx "PcB" i) (pctx "PcA" i))
                                d         (v/assert kb (list 'not back-edge) 'CxUniverse
                                                    {:strength :monotonic})
                                h         (v/assert kb (list 'genlCx (pctx "PcA" i) (pctx "PcB" i))
                                                    'CxUniverse {})]
                            (v/retract! kb d)
                            h))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))

(defn- retract-merge-scaling
  "One `retract!` of a fact naming no merged term, on a KB carrying n standing `sameAs`
  merges.

  The second teardown check beside `retract-nat-scaling`, and it exists for the reason
  that one does: a settle reconciles derived state, and the population that state is
  drawn over is not a fixed small thing.  `sameAs` is one of three relations feeding the
  equality closure (docs/equality.md), `owl:sameAs` is what an RDF import emits in
  quantity, and a reconcile that re-examines every displaced spelling per settle makes
  loading n merges quadratic in n — while every other check in this file, carrying zero
  merges, reads perfectly flat with that cost in place.

  Each of the n merges displaces exactly **one** stored fact: the fact is written under
  the larger spelling and the content-keyed election puts the smaller one on top, so the
  standing displaced set is n and the KB is otherwise inert.  The victims name none of
  them — plain binary facts of fresh individuals — so no timed retraction moves the
  closure, and every reading is the same removal doing the same work."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pMergeBorn (symbol (str "PMHi" i)) 'PMPlace) 'CxPerf {})
        (v/assert kb (list 'sameAs (symbol (str "PMAa" i)) (symbol (str "PMHi" i)))
                  'CxPerf {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pMergeVictim (symbol (str "PMV" i)) 'PMVal)
                                    'CxPerf {}))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))

(def ^:private edge-writes
  "Taxonomy edges written per run, for the same reason `retract-victims` is what it is: an
  edge handle can only be written once, so the timed operation needs a supply of distinct
  edges, and there have to be more of them than `tail-samples` takes.  **The same count at
  both sizes**, so each answer is the mean of the last fifty over windows of equal width,
  and each edge is its own fresh pair of terms — re-asserting an active edge is a no-op
  that bumps no generation and would time nothing."
  60)

(defn- genl-edge-negation-recheck
  "One `genl` edge under a fresh subtype, on a KB whose single excepted rule carries a
  **negated** conjunct and has already fired n times.

  A negated exception conjunct registers in the re-check index under the functor `not`,
  which hides the predicate it is about, so a `genl` edge cannot be keyed on it the way
  every other conjunct is.  Queueing such a rule unconditionally means one level-6
  exception query per firing it ever made, per edge written anywhere in the KB — a cost
  proportional to the rule's history rather than to the edge, and a taxonomy load
  quadratic against a KB carrying one ordinary `(exceptWhen (not …) …)`.

  The edges are the thing measured and the firings are the background: each edge's
  subtype is fresh and nothing is below it, its supertype is named by no exception, and
  the negated conjunct is about a predicate neither of them reaches.  So no edge can
  change what the rule's exception answers at either size, and what the readings differ
  by is only how many firings were re-decided anyway."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(exceptWhen (not (p_neg_skip ?x))
                              (set/defaultRule (implies (and (p_neg_probe ?x)) (p_neg_seen ?x))))
              'CxPerf {})
    (doseq [i (range n)]
      (v/assert kb (list 'p_neg_probe (symbol (str "PNG" i))) 'CxPerf {}))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl (symbol (str "pnegv" i "_t")) 'pnegtop_t)
                              'CxPerf {:strength :monotonic}))))))

(defn- taxonomy-edge-arbitration
  "One `genl` edge — a fresh subtype under a fresh supertype, with nothing above it,
  nothing below it and no separation anywhere near it — written on a KB carrying n
  standing definitional dilemmas.

  `clash-arbitration` builds that standing set and then never writes a taxonomy edge, so
  the whole of its run reads one clash vocabulary and the memo's staleness test is never
  asked a question.  This is the workload that asks it.  Every edge activation bumps the
  relation's generation, and a memo retired on that generation abandons its whole carry
  per edge: two `checks/arbitrable-violations` calls per standing pair, on a KB where the
  edge separates nothing and reaches no instance.

  Ω(standing) is the floor here as it is there — a settle republishes the whole standing
  clash set either way — so the bound is the same claim in the same shape: the per-pair
  term must stay bookkeeping rather than a re-derivation of the checks.

  The dilemmas are built under one deferred settle: the standing set is the KB this
  measures against and not the thing being measured, and building it an assert at a time
  is the Ω(standing)-per-settle cost paid n times over."
  [n]
  (binding [checks/*arbitrate-constraints?* true]
    (let [kb (fresh-kb)]
      (v/assert kb '(disjoint pea_t peb_t) 'CxPerf {:strength :monotonic})
      (v/with-deferred-settle kb
        (doseq [i (range n)
                :let [x (symbol (str "PEX" i))]]
          (v/assert kb (list 'pea_t x) 'CxPerf {})
          (v/assert kb (list 'peb_t x) 'CxPerf {})))
      (doall
       (for [i (range edge-writes)]
         (nanos (v/assert kb (list 'genl (symbol (str "pev" i "_t"))
                                   (symbol (str "peu" i "_t")))
                          'CxPerf {:strength :monotonic})))))))

(defn- arity-reach-under-subtree
  "One `genl` edge putting a subtree of `n` predicates — each holding one stored fact —
  under a predicate whose arity is declared, so the edge binds a length to every one of
  them at once.

  The retroactive arity report's own shape, and the axis no other check varies.  The
  report descends the predicate hierarchy: a binding arriving at the top convicts the
  facts of everything beneath it, so the sweep is over the arriving predicate's **spec
  subtree** rather than over one posting list, and `genl` is the commonest edge there is.
  `taxonomy-edge-arbitration` above writes an edge with nothing below it, which is
  exactly the case this cost does not appear in.

  Ω(subtree) is the floor: the facts a binding convicts are the subtree's facts, and
  finding them is the work.  So the claim is linear rather than flat, and the bound is
  what separates linear from the quadratic of a sweep whose reach is re-derived per
  predicate instead of once for the pass.  The two cheap guards are what keep the common
  case off this curve, and neither shows up in the ratio: a subtree of predicates holding
  no facts costs one index **count** each, and the whole pass is skipped for a KB that
  declares no arity at all.

  **The subtree has a second reader on the assert path, and the ratio cannot tell the two
  apart.**  `special/subsumption-seeds` walks the same spec closure for the same edge, one
  posting per predicate, because an edge makes the facts under it matchable at a supertype
  they did not have — and it is unconditional, where the arity sweep is behind
  `any-arity-declared?`.  Measured on this workload the two are half the reading each:
  n=256 costs 3.039 ms with an arity declared and 1.526 with none, so the sweep owns 50% of
  it and the linear floor is jointly owned.  What follows is that a green run here says the
  *pair* stayed linear, and that removing the sweep entirely would still leave this check
  reading linear — the attribution the bound makes is between linear and quadratic, not
  between the two passes.

  Each timed edge needs its own subtree — an edge is written once, and re-asserting an
  active one is a no-op that sweeps nothing — so the build dominates the run and none of
  it is timed."
  [n]
  (let [kb (fresh-kb)]
    (doall
     (for [i (range edge-writes)
           ;; camelCase throughout: these carry binary facts, and a snake_case functor
           ;; names a type and is legal only as a unary predicate
           :let [root (symbol (str "parsRoot" i))
                 mid  (symbol (str "parsMid" i))]]
       (do
         (v/assert kb (list 'binary_predicate root) 'CxPerf {:strength :monotonic})
         ;; the subtree is what this measures against, not what it measures
         (v/with-deferred-settle kb
           (doseq [j (range n)
                   :let [p (symbol (str "parsSub" i "x" j))]]
             (v/assert kb (list 'genl p mid) 'CxPerf {:strength :monotonic})
             (v/assert kb (list p 'PARSA 'PARSB) 'CxPerf {})))
         (nanos (v/assert kb (list 'genl mid root) 'CxPerf {:strength :monotonic})))))))

(def ^:private settles-per-batch-reading
  "Deferred batches timed per run of `arity-reach-batch-roots`.  Fewer than `tail-samples`
  and **the same count at both sizes**, so each answer is the mean of all of them over
  windows of equal width: one batch at the large size is tens of milliseconds, and fifty of
  them over five measurement passes is a minute of gate for one check.  Nothing accumulates
  between batches — each writes its own chain, and the roots of a settle are that batch's
  own edges — so an average over the whole run and an average over its tail are the same
  answer here."
  20)

(defn- arity-reach-batch-roots
  "One settle over a deferred batch of n `genl` edges forming a chain, on a KB declaring
  one arity.

  **The axis every other check holds at one.**  `arity-bound-by` makes the `sub` of every
  `(genl sub super)` a root of the retroactive arity pass, and the pass expands each root
  into its whole spec subtree.  The result is a set, so it dedups; the *walk* does not, and
  the roots of one settle sit on top of one another when the batch is a hierarchy — which
  is what a batch of taxonomy edges is.  Every check beside this one writes a single edge
  per settle, where the two numbers are the same.

  The **asserts are outside the reading**, which is what makes the reading the pass rather
  than the load: the batch is written under `wiring/*defer-settle?*` with the depth repair
  deferred beside it — `v/with-deferred-settle`'s own two bindings — and what is timed is
  the settle that macro would run at the end.  Nothing in the chain holds a fact, so no
  sweep examines one and `*exposure-instance-budget*` is never spent: the whole of what is
  measured is the expansion of the roots, which is the part no budget bounds.

  A chain rather than a fan, because depth is the multiplier: the subtrees of n edges under
  one root sum to n across a fan of depth one and to n²/2 along a chain, and an ontology's
  `genl` edges arrive as a hierarchy somewhere between the two.  So the reading is what a
  batch costs at the worse end of that range — which is the end a load sits at.

  It read 59x when it was written, and the check is why: the pass expanded each root on
  its own, and `tax/specs`' memo cannot span roots, since it is keyed on the node a walk
  began at.  `tax/specs-of-all` walks the union once instead and the reading is 7-11x.
  What this guards now is that the union stays a union: expand per root again, by any
  route, and a batch of taxonomy edges is quadratic again.

  The bound is calibrated against **two** measured defects rather than one, and the second
  is the reason it is not looser: the per-root expansion reads 63.6x, and a partial fix
  that unions the subtrees before counting them while still expanding each one reads 47.0x.
  That partial fix is worth 15% and looks from the code like the whole answer — the union
  is right there in the source — so a bound set between the two would pass it."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(binary_predicate parbTop) 'CxPerf {:strength :monotonic})
    (doall
     (for [b (range settles-per-batch-reading)]
       (do
         (binding [wiring/*defer-settle?* true
                   tax/*defer-depths?*    true]
           (v/assert kb (list 'genl (symbol (str "parb" b "x0")) 'parbTop)
                     'CxPerf {:strength :monotonic})
           (doseq [i (range 1 n)]
             (v/assert kb (list 'genl
                                (symbol (str "parb" b "x" i))
                                (symbol (str "parb" b "x" (dec i))))
                       'CxPerf {:strength :monotonic})))
         (nanos (settle/settle kb)))))))

(defn- arity-context-edge-side
  "A `genlCx` edge whose **below** end holds n facts and whose **above** end holds none,
  written on a KB declaring one arity.

  A context edge supplies an arity binding while naming no predicate — what it moves is
  what a stored fact's own vantage can see — so the pass has to find the predicates itself,
  and the edge's reach has two ends that are each complete on their own: the facts below
  `sub`, and the bindings above `super`.  It sizes both off `count-in-context` and
  enumerates the smaller.

  **The choice is required and picking wrong is silent**, which is what earns it a
  check.  The shipped ontology writes `(genlCx CxUniverse CxMeasure)` and seven more like
  it: everything sees `CxUniverse`, so the below end of that edge is the whole KB and the
  above end is one file's vocabulary.  A pass that always took the end below would answer
  the same thing and read the entire store to do it, once per such edge, and no test would
  say a word.

  Here the end below is a context carrying n facts and the end above is a fresh context
  carrying none, so the reading is flat exactly while the smaller end is the one walked and
  tracks n the moment it is not.  Distinct subjects under one predicate, so nothing the
  walk reaches is a violation: this measures the reach, not the report."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(binary_predicate pacFact) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pacFact (symbol (str "PAC" i)) 'PACval) 'CxAcBig {})))
    (doall
     (for [i (range edge-writes)]
       (nanos (v/assert kb (list 'genlCx 'CxAcBig (pctx "AcW" i))
                        'CxPerf {:strength :monotonic}))))))

(def ^:private capped-subtree-predicates
  "Predicates under the binding in `arity-reach-budget-cap`, each holding the size's worth
  of facts.  More than one, because what the pass spends past the cut is one element
  realized per predicate the budget never reached, and a subtree one predicate wide would
  have none of them."
  8)

(defn- arity-reach-budget-cap
  "A binding edge flipped in and out of belief over a subtree holding n facts per predicate,
  with `*exposure-instance-budget*` bound to 100.

  `arity-reach-under-subtree` measures the sweep **below** the cap, where the cost is the
  subtree and is meant to be.  This measures it above: past the cut, 8x the facts behind a
  binding costs the same, which is the claim a budget exists to make and the only one it
  can support.

  **The cap bounds half of what the pass spends, and this pins the half it bounds.**  The
  budget counts *facts examined*, and the predicates are counted before it is consulted at
  all: the subtree is expanded and cardinality-read in full first, and past the cut every
  remaining predicate still realizes one element of its posting — a read and a record fetch
  apiece — to learn that it has been cut.  Both are a function of the subtree's **width**,
  so that is held at `capped-subtree-predicates` while the facts behind it move.

  The edge is defeated and revived rather than written once, for the reason
  `taxonomy-belief-flip` flips one: a `genl` edge is a no-op on re-assert, and every
  revival puts it back in the moved region to sweep again over a KB that has not grown.
  The edge carries the strength difference — written at `:default` so the monotonic
  negation defeats it, exactly as that check builds its own."
  [n]
  (binding [tax/*exposure-instance-budget* 100]
    (let [kb (fresh-kb)]
      (v/assert kb '(binary_predicate pabcRoot) 'CxPerf {:strength :monotonic})
      (v/with-deferred-settle kb
        (v/assert kb '(genl pabcMid pabcRoot) 'CxPerf {})
        (doseq [j (range capped-subtree-predicates)
                :let [sub (symbol (str "pabcSub" j))]]
          (v/assert kb (list 'genl sub 'pabcMid) 'CxPerf {})
          (doseq [i (range n)]
            (v/assert kb (list sub (symbol (str "PABC" i)) 'PABCval) 'CxPerf {}))))
      (let [edge '(not (genl pabcMid pabcRoot))]
        (doall
         (for [_ (range edge-writes)]
           (nanos (let [h (v/assert kb edge 'CxPerf {:strength :monotonic})]
                    (v/retract! kb h)))))))))

(defn- constraint-genl-edge
  "A `genl` edge flipped in and out of belief above a predicate holding n facts, on a KB
  declaring `functional` — either **on** the predicate above the edge or on one the edge
  cannot reach.  `budget` is what `*exposure-instance-budget*` is bound to.

  The cross-context constraint report reaches out of the moved region for two edges, and
  this is the second of them: a `functional` or `asymmetric` mark standing on a
  super-predicate descends a new `(genl sub super)` edge to a subtree that never carried
  one, so a pair of `sub` facts either side of a visibility edge starts clashing without
  any context moving.  What that implicates is the subtree's facts, and `genl` is the
  commonest edge an ontology writes — so the arm is gated on a mark actually being at or
  above `sub`, which costs a `props-over` read on an edge under nothing marked.

  The flip is what isolates the settle's own reading.  A `genl` edge on the way *in* also
  walks the same subtree at `special/subsumption-seeds`, unconditionally and whatever the
  marks say, so an edge written once measures both passes and can separate neither; a
  revival puts the edge back in the moved region without going through that path, and the
  reading is the constraint pass alone.  The mark is declared either way, so the report's
  vocabulary gate is open in both shapes and the only difference is the one being measured."
  [marked? budget]
  (fn [n]
    (binding [tax/*exposure-instance-budget* budget]
      (let [kb (fresh-kb)]
        (v/assert kb (list 'functional (if marked? 'pcegTop 'pcegElse))
                  'CxPerf {:strength :monotonic})
        (v/with-deferred-settle kb
          (v/assert kb '(genl pcegMid pcegTop) 'CxPerf {})
          (v/assert kb '(genl pcegSub pcegMid) 'CxPerf {})
          (doseq [i (range n)]
            (v/assert kb (list 'pcegSub (symbol (str "PCEG" i)) 'PCEGval) 'CxPerf {})))
        (let [edge '(not (genl pcegMid pcegTop))]
          (doall
           (for [_ (range edge-writes)]
             (nanos (let [h (v/assert kb edge 'CxPerf {:strength :monotonic})]
                      (v/retract! kb h))))))))))

(defn- context-edge-arbitration
  "One `genlCx` edge — a fresh context under `CxUniverse`, with nothing below
  it — written on a KB carrying n standing P/¬P dilemmas, every one of them stated in a
  context the edge does not reach.

  The negation twin of the check above, and the same blind spot in the same place:
  `negation-arbitration` builds its standing set and writes no context edge afterwards.
  Joint visibility is read through the `genlCx` closure, so a memo retired on that
  relation's generation re-derives every opposed body per edge — two belief-filtered
  reads and a cross product apiece — for an edge no contradiction in the KB is stated
  anywhere near.

  No separation anywhere, so the clash memo short-circuits and this is the negation
  pairing alone."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [pr (symbol (str "pceg" i))
                    x  (symbol (str "PCE" i))]]
        (v/assert kb (list pr x) 'CxPerf {})
        (v/assert kb (list 'not (list pr x)) 'CxPerf {})))
    (doall
     (for [i (range edge-writes)]
       (nanos (v/assert kb (list 'genlCx (symbol (str "CxPCtx" i))
                                 'CxUniverse)
                        'CxPerf {:strength :monotonic}))))))

(def ^:private reads-per-visibility-reading
  "Reads batched into one timed measurement, the same batch at both sizes so it cancels
  out of the ratio — `reads-per-clash-reading`'s idiom, for its reason."
  20)

(defn- visibility-reading
  "A scoped read on a KB carrying n believed `(except (sentexHandle H))` facts, all
  visible from the reading context.

  The claim is that the read costs **what it returns**, not what the KB hides. Every
  scoped retrieval filters by visibility removal (`res/without-excepted`), and the answer
  that filter needs is *which handles are hidden from here* — a question whose honest
  shape is a lookup per match and whose lazy shape is a walk over every `except` in the
  KB, per call. The excepts here hide **decoys** the read never returns, so n moves the
  filter's input while leaving its output alone, and a reading that grows with n is the
  filter re-deriving what the store already knows.

  **The literal cache is bound off**, and that is the point rather than a distortion.
  A repeat read under an unmoved clock is served whole from `literal-cache`, so leaving
  it on would measure the cache and report the filter as free at both sizes. The caller
  this check exists for is forward chaining, which moves the clock per placement and so
  meets this read cold every time (`literal-cache/lookup` states that directly).

  Built under one deferred settle: the excepts are the KB this measures against, not the
  thing measured."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [h (v/assert kb (list 'pv_decoy (symbol (str "PVD" i))) 'CxPerf
                                {:strength :monotonic})]]
        (v/assert kb (list 'except (sx/sentex-handle h)) 'CxPerf
                  {:strength :monotonic})))
    (v/assert kb '(pv_seen PVOne) 'CxPerf {:strength :monotonic})
    (binding [lc/*enabled* false]
      (doall
       (for [_ (range 60)]
         (nanos (dotimes [_ reads-per-visibility-reading]
                  (count (v/sentexes-matching kb '(pv_seen ?x) 'CxPerf)))))))))

(def ^:private readings-per-reader-fan
  "Timed readings.  Above `tail-samples`, so the answer is a mean over the last 50 and the
  first reading — the only one that still has merges to derive — is outside it."
  60)

(defn- genlcx-edge-reader-fan
  "One `(genlCx sub super)` edge joining two branches of a KB carrying n **bystander**
  reader contexts — contexts that read the candidates' own branch and sit under no `sub`,
  so the edge leaves every one of their ancestor sets exactly as it found them.

  The claim is that the edge costs the readers it **widened**.  When the edge lands,
  `special/equate-under-context-edge` re-derives the functional equalities over the facts
  the widened ancestor set newly exposes, and each derivation sweeps a set of reader
  contexts: the honest set is `context-down(sub)`, which here is `sub` alone, and the lazy
  one is every reader below each candidate's own storage context, which every bystander
  is.  So n moves the reader fan and leaves the widened set and the candidate set alone,
  and an edge that grows with n is the sweep re-asking readers a question already answered
  when the fact arrived.

  **This is the growth that shipped**: as the starter grew from 1,668 to 2,435 sentexes
  one edge over it went from 23 ms to 145 ms and `starter/load-into` from 0.87 s to
  2.50 s.  `genlcx_sweep_cost_test` counts the same fan in the suite; this reads it as a
  duration, which is what also catches a per-call cost growing inside a fan of the right
  size.

  **One `sub` exists at a time, and the reading retracts its own edge.**  That is what
  keeps the baseline out of the measurement, and getting it wrong once is why it is
  written down: a `sub` per reading has to be wired somewhere it can see the candidates,
  which makes each one a bystander of every later reading — 60 of them, so the n=8 fan is
  really 68 and the n=512 fan 572, and a ratio the sweep should have made ~57x reads
  2.0x.  That is the header's own warning about a baseline that already carries the cost,
  met in the setup rather than in the sizes.  Retracting the joining edge leaves the merge
  standing (`equate-under-context-edge` says why), so every reading after the first pays
  the sweep and not the merge — which is the fan, and is the quantity this is about."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(functional gefParent) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(genlCx CxGefLeft CxUniverse) 'CxCore {:strength :monotonic})
    (v/assert kb '(genlCx CxGefRight CxUniverse) 'CxCore {:strength :monotonic})
    (v/with-deferred-settle kb
      ;; readers of the candidates' branch, under no `sub`: the joining edge changes no
      ;; ancestor set of theirs, so none of them is entitled to cost it anything
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxGefBy" i)) 'CxGefLeft) 'CxCore
                  {:strength :monotonic}))
      ;; the one sub, and the clashing pairs the sweep enumerates
      (v/assert kb '(genlCx CxGefSub CxGefLeft) 'CxCore {:strength :monotonic})
      (doseq [i (range 8)]
        (v/assert kb (list 'gefParent (symbol (str "GefK" i)) (symbol (str "GefA" i)))
                  'CxGefLeft {:strength :monotonic})
        (v/assert kb (list 'gefParent (symbol (str "GefK" i)) (symbol (str "GefB" i)))
                  'CxGefRight {:strength :monotonic})))
    (doall
     (for [_ (range readings-per-reader-fan)]
       (let [t (nanos (v/assert kb '(genlCx CxGefSub CxGefRight) 'CxCore
                                {:strength :monotonic}))]
         (v/retract! kb (v/handle-of kb '(genlCx CxGefSub CxGefRight) 'CxCore))
         t)))))

(def ^:private reads-per-clash-reading
  "Readings of the standing set batched into one timed measurement, and **the same batch
  at both sizes**, so it cancels out of the ratio.  A single read at the small size lands
  around `noise-floor-ns`, where a ratio is jitter; a fixed batch is what lifts the
  measurement clear of the floor without changing what it measures, exactly as
  `arg-root-retrieval` times a hundred matches rather than one."
  10)

(defn- standing-clash-reading
  "`core/contradictions` on a KB carrying n standing P/¬P dilemmas — the **read** side of
  the standing set whose write side `negation-arbitration` measures, over the same KB
  shape.

  A reading is `settle/ranked` over what the last settle published.  The stored vectors
  are in arrival order, so putting them in content order is what makes
  `(first (contradictions kb))` an answer about the knowledge rather than about which
  pair was typed first — and it is done at the read because a KB is written to far more
  often than it is read (`settle/record-clashes!` carries that measurement).  That moves
  the cost onto a path with no other check on it, which is what this is.

  `contradictions` rather than `conflicts` because a default/default pair is a dilemma;
  the two are one call, and `core/preview`'s standing filter is a third caller of it.

  The dilemmas are built under one deferred settle: they are the KB this measures
  against, not the thing being measured, and building them an assert at a time is the
  Ω(standing)-per-settle cost `negation-arbitration` is for."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [pr (symbol (str "pread" i))
                    x  (symbol (str "PRD" i))]]
        (v/assert kb (list pr x) 'CxPerf {})
        (v/assert kb (list 'not (list pr x)) 'CxPerf {})))
    (doall
     (for [_ (range 60)]
       (nanos (dotimes [_ reads-per-clash-reading]
                (count (v/contradictions kb))))))))

(def ^:private inherit-chain-depth
  "How far above the claim-holders the preserved relation runs, so that **one reach walk
  is a real cost** rather than a lookup: `fact-reach` reads the store once per node it
  walks, and a reach thirty-three nodes long is what puts the walking above the comparing
  in the reading below.  With a one-node reach the cross-product would dominate at both
  sizes and the check would read the same number whether the memo was there or not."
  32)

(defn- inherit-reach-memo
  "`ask?` on a preserved goal about a term that n incomparable claims reach, each of them
  holding a reach thirty-two hops long.

  `undercut?` compares every claim against every other and each comparison asks for a
  claim's reach, so the **walks** are quadratic in the claims unless something remembers
  them.  `inherit/*memo*` is what does, for the length of one question: n distinct reaches
  are walked once each, and the n² comparisons that follow are set lookups.  So the cost
  is the walking — linear in the claims — plus a cross-product that stays cheap, and 8x
  the claims must land near 8x rather than near the 64x a lost memo reads.

  The counted companion is `inherit_test/the-reach-walk-is-linear-in-the-claims-and-not
  -quadratic`, which reads the same claim off `matches-visible` call counts rather than off
  a clock, and can see it at any depth."
  [n]
  (let [kb    (fresh-kb)
        base  'PiPart
        above (mapv #(symbol (str "PiAbove" %)) (range inherit-chain-depth))]
    (v/with-deferred-settle kb
      (v/assert kb '(transitive piPartOf) 'CxPerf {:strength :monotonic})
      (v/assert kb '(transitiveInArg pi_needs_work 1 piPartOf) 'CxPerf {:strength :monotonic})
      ;; the shared chain every claim-holder's reach runs up
      (doseq [[a b] (partition 2 1 above)]
        (v/assert kb (list 'piPartOf a b) 'CxPerf {}))
      (doseq [i (range n)
              :let [o (symbol (str "PiWhole" i))]]
        (v/assert kb (list 'piPartOf base o) 'CxPerf {})
        (v/assert kb (list 'piPartOf o (first above)) 'CxPerf {})
        (v/assert kb (list 'pi_needs_work o) 'CxPerf {})))
    (let [goal (list 'pi_needs_work base)]
      (doall (for [_ (range 60)]
               (nanos (v/ask? kb goal 'CxPerf)))))))

(defn- qcn-network-residency
  "A `possible-relations` call on a fixed six-region containment chain, asked repeatedly,
  on a KB holding n *more* facts of the same spatial predicate in a context the asker
  cannot see.

  The network the call reads is the same size at both n — six regions, one closure — so
  what the reading tracks is the **read**, never the pass.  A resident network is taken
  off the KB's `:qcn` atom and rebuilt only when the change clock moves
  (`observe/cached`), so a repeat costs a map lookup; reading the KB again per call would
  walk the predicate's whole extent, which is exactly the n that grows here.
  docs/qcn.md counts that difference as seventeen thousand reads against thirty-nine
  asserts, taken down to seventy-eight.

  **The extra facts sit in a sibling context on purpose.**  A check whose visible network
  grew with n would be measuring the path-consistency pass, which is superquadratic by
  design and is nobody's claim to hold flat — the growth would swamp the read and the
  bound would have to be loose enough to see nothing.  A sibling context is invisible from
  the asking one, so the pass is identical at both sizes and the extent a rebuild would
  walk is the only thing that moved.

  The counted companion is `qcn_chain_test/network-reads-grow-with-the-calls-and-not-with
  -the-asserts`, which holds the *number* of builds where this holds their cost."
  [n]
  (let [kb    (fresh-kb)
        chain (mapv #(symbol (str "PqRegion" %)) (range 6))]
    (v/add-prover kb (space/spatial-prover))
    (v/assert kb '(genlCx CxPerfQcn CxUniverse) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(genlCx CxPerfQcnSide CxUniverse) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [[a b] (partition 2 1 chain)]
        (v/assert kb (list 'nonTangentialProperPart a b) 'CxPerfQcn {:strength :monotonic}))
      (doseq [i (range n)]
        (v/assert kb (list 'nonTangentialProperPart
                           (symbol (str "PqOtherA" i)) (symbol (str "PqOtherB" i)))
                  'CxPerfQcnSide {:strength :monotonic})))
    ;; build and close once, outside the loop: the first read is the pass, and timing it
    ;; would gate the closure's cost instead of the repeat's
    (v/possible-relations kb :rcc8 'CxPerfQcn (first chain) (peek chain))
    (doall
     (for [_ (range 60)]
       (nanos (dotimes [_ 200]
                (v/possible-relations kb :rcc8 'CxPerfQcn (first chain) (peek chain))))))))

(def ^:private metric-arrivals
  "How many constraints arrive one at a time in `metric-closure-warm-start` — the same
  count at both sizes, since the reading is per arrival."
  25)

(defn- metric-closure-warm-start
  "A chain of n instants, closed, and then 25 more instants arriving one constraint at a
  time with the gap back to the head of the chain read after each — a timeline being
  loaded, which is the structure that puts a closure in front of every fact.

  **Pure data, and deliberately.**  `stp/close-state-from` knows nothing about a KB, so
  what this measures is the algorithm and not the belief read in front of it; that the
  engine actually reaches it is `stp_test/an-arriving-constraint-is-relaxed-into-the-answer
  -already-held`, which counts the two routes through `stp/closure`. Splitting them is what
  keeps the ratio a claim about the pass — a KB read is linear in the stated constraints
  and would sit in the denominator at both sizes flattering neither.

  **Not a flat claim, and the bound says which claim it is instead.**  A closure is a
  bound between every pair of instants, so an arriving constraint costs at least the pairs
  it moves and is quadratic in the instant count however it is reached.  What the warm
  start removes is the *pass*, and the bound is where the two shapes separate."
  [n]
  (let [inst  #(symbol (str "Pmt" %))
        base  (reduce (fn [net i] (stp/narrow net (inst i) (inst (inc i)) 8 12))
                      {} (range (dec n)))
        head  (inst 0)]
    (loop [net base, state (stp/close-state base (stp/nodes base)), i 0, acc []]
      (if (= i metric-arrivals)
        acc
        (let [p     (inst (+ n i -1))
              q     (inst (+ n i))
              net'  (stp/narrow net p q 8 12)
              nodes (stp/nodes net')
              box   (volatile! nil)
              t     (nanos (vreset! box (stp/close-state-from net' state nodes)))]
          (stp/constraint (:net @box) head q)
          (recur net' @box (inc i) (conj acc t)))))))

;; ---- the one check that writes to a disk ---------------------------------
;;
;; Every check above runs on `fresh-kb`, which is `:backend :memory`, so nothing in this
;; file has ever priced the durable stores — and `assert_cost_test`, the counted gate
;; beside it, is pinned to the memory backend for its own reason.  The write-ahead logs,
;; the idx slots and the batching between them are gated by neither.

(defn- delete-tree!
  [^java.io.File file]
  (when (.isDirectory file)
    (doseq [child (.listFiles file)] (delete-tree! child)))
  (.delete file))

(defn- perf-disk-dir ^java.io.File []
  (java.io.File. (str (System/getProperty "java.io.tmpdir") "/vaelii-perf-disk")))

(defn- fresh-disk-kb
  "An empty `:backend :disk-log` KB in a directory of its own — `fresh-kb`'s durable twin.
  Wiped **before** the open as well as after the close, so a run interrupted part way
  leaves nothing for the next one to measure against."
  []
  (let [dir (doto (perf-disk-dir) (delete-tree!) (.mkdirs))]
    (v/open-kb {:backend :disk-log :dir (.getAbsolutePath dir) :recover? false})))

(defn- durable-fact-append
  "n facts of one predicate onto a disk-backed KB, timed per assert.

  Every quantity the durable write path spends per record is fixed by construction — one
  log frame and one idx slot per record, one packed WAL append for the whole batch of
  index ops a sentex generates — so the reading should not move between the two sizes at
  all.  What can move it is the **set** behind the predicate root, which grows to n: the
  index WAL logs the op (`[:add-to-set k m]`, one member) rather than the resulting value,
  and a frame carrying the grown set instead would make a linear load quadratic.
  `vaelii.impl.disk.kv` records that shape as the reason for logical logging, and this is
  the check that would notice it coming back.

  One predicate throughout, so that root is the hot one; distinct subjects, so no
  cross-context or partner pass has anything to reach for and what is measured is
  storage.  `:chain? false` for the same reason — no rule exists to fire, and the KB is
  built by the very operation being timed.

  Closed on the way out, and the directory removed after it: the file lock and the
  durability daemon's registration both belong to the directory, and a check that left
  them would have every later check's wall-clock crossed by an fsync of a store nothing
  is using — and the gate would leave a few megabytes of log behind every time it ran."
  [n]
  (let [kb (fresh-disk-kb)]
    (try
      (doall
       (for [i (range n)]
         (nanos (v/assert kb (list 'pdFact (symbol (str "PdA" i)) i) 'CxPerf
                          {:chain? false}))))
      (finally
        (v/close! kb)
        (delete-tree! (perf-disk-dir))))))

(def checks
  ;; The one bound here that is not *flat*, and deliberately.  A settle republishes the
  ;; whole standing clash set, so its cost is Ω(standing) by construction and no memo
  ;; makes an assert free of what is standing.  What the gate defends is that the per-pair
  ;; term stays **bookkeeping** rather than a re-derivation of the checks, and the
  ;; measured separation says it does: 9.5x with both memos in place, 12.3x with the
  ;; report memo removed, 46.5x with the carry-forward removed as well — the structure that
  ;; actually shipped.  15x catches that with three times over on the big one.
  ;;
  ;; The baseline is 25 rather than 100 because it has to be a size at which almost
  ;; nothing is standing.  At 100 the baseline already carried a hundred pairs' worth of
  ;; the very per-pair cost being measured, which divided out of the ratio and left the
  ;; three variants reading 6.1 / 7.5 / 9.2 — a 12x difference in what matters, compressed
  ;; into a 1.5x spread the bound could not have separated.
  [{:name      :clash-arbitration
    :claim     "32x the standing clashes costs under 15x per assert — bookkeeping, not a re-derivation each"
    :sizes     [25 800]
    :max-ratio 15.0
    :run       clash-arbitration}

   {:name      :constraint-exposure-shared-arg
    :claim     "asserting into a declared-asymmetric slot costs what the region holds, not what the KB does"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       constraint-exposure-shared-arg}

   {:name      :constraint-exposure-context-edge
    :claim     "past the instance cap, 8x the facts behind a genlCx edge costs the same"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       constraint-exposure-context-edge}

   {:name      :unrelated-fact-under-marked-kb-fanout
    :claim     "an unrelated predicate's assert is flat in the genlCx fanout below its context, however many other predicates elsewhere carry a functional mark"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       unrelated-fact-under-marked-kb-fanout}

   {:name      :functional-in-arg-empty-determinant-sweep
    :claim     "past the instance cap, 8x the facts under an empty-determinant functionalInArg mark costs the same per assert"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       functional-in-arg-empty-determinant-sweep}

   {:name      :defeasible-load
    :claim     "a fact arriving through a defeasible rule costs the same at 2000 as at 250"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       defeasible-load}

   {:name      :taxonomy-depth
    :claim     "a genl edge costs the same 2000 deep in a chain as 250 deep"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       taxonomy-depth}

   {:name      :taxonomy-belief-flip
    :claim     "defeating and reviving one genl edge costs the same in a 4000-edge taxonomy as in a 500-edge one"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       taxonomy-belief-flip}

   {:name      :flat-cache-belief-flip
    :claim     "defeating and reviving one disjoint declaration costs the same in a KB declaring 4000 of them as in one declaring 500"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       flat-cache-belief-flip}

   {:name      :arg-root-retrieval
    :claim     "100 patterns pinning an argument after a variable are flat in the extent"
    :sizes     [400 3200]
    :max-ratio 2.0
    :run       arg-root-retrieval}

   {:name      :closure-membership
    :claim     "one pair's membership in a closure already asked is flat in the chain's length"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       closure-membership}

   {:name      :membership-check
    :claim     "asserting a type membership is flat in how many the KB already holds"
    :sizes     [200 1600]
    :max-ratio 2.0
    :run       membership-check}

   {:name      :membership-under-depth
    :claim     "32x the hierarchy above a predicate costs under 12x per membership assert — one retrieval per super, so it grows with the depth and must stay well under it"
    :sizes     [8 256]
    :max-ratio 12.0
    :run       membership-under-depth}

   {:name      :disjoint-enumeration
    :claim     "an open disjointness goal is flat in the vocabulary it is not about"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       disjoint-enumeration}

   {:name      :disjoint-clique-membership
    :claim     "a membership assert whose type sits in a sibling-disjoint clique is flat in the clique size"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       disjoint-clique-membership}

   {:name      :disjoint-metatype-membership
    :claim     "a membership assert whose type belongs to a disjoint_metatype is at most linear in the member count, never quadratic"
    :sizes     [500 4000]
    :max-ratio 12.0
    :run       disjoint-metatype-membership}

   {:name      :compound-probe
    :claim     "100 find-sentexes on a compound are flat in the extent of the hot atom it names"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       compound-probe}

   ;; The negation twin of `clash-arbitration`, and the same reasoning picks its numbers:
   ;; Ω(standing) is the honest floor (a settle republishes the whole set), the baseline is
   ;; small enough that almost nothing is standing at it, and the bound separates
   ;; bookkeeping-per-pair from re-derivation-per-pair.  Re-deriving every standing pair
   ;; per settle round measured 38.9x here — the structure that shipped, and the one `:opposed`
   ;; was believed to have removed.  It removed a different one: the *scan of every stored
   ;; negation*, which is the commoner workload and is what `negation-load` below still
   ;; holds flat.  Neither check subsumes the other, and only both together say the pass is
   ;; not paying for the standing set (see docs/nmtms.md).
   ;;
   ;; **The baseline is 100 and not 25, and the bound sits above the size ratio, because
   ;; that combination is the only one a constant-term win cannot break.**  Reading
   ;; `a + b·n`, the ratio is `(a + 800b) / (a + 100b)`, which is strictly *below* 8 for
   ;; every positive `a` and approaches 8 as `a` falls.  So no improvement to the fixed cost
   ;; of a settle can walk this check upward, however far that cost falls: what is left to
   ;; cross the bound is the per-pair term going super-linear, which is what the claim is
   ;; about.  That argument bounds the *constant's* contribution and not the whole reading,
   ;; so the bound is set from measurement rather than from the model: four full runs read
   ;; 6.63x, 7.58x, 7.74x and 8.36x, the last of them above the model's own ceiling.  The
   ;; spread is the large end — n=800 moves ten percent and more between runs where n=100
   ;; moves one — so 11 is the worst of those with room, and a re-derivation regression
   ;; reads several times it rather than a few percent over.
   ;;
   ;; A baseline of 25 gave the ratio an asymptote of 32 against a bound of 12, which is
   ;; 20x of room for a constant-term win to spend: the fixed cost is ~0.04 ms against
   ;; ~0.0017 ms a pair, so at 25 pairs the reading is mostly constant, and shaving it walks
   ;; the ratio from 10x toward 17x while every absolute number improves.  A check that
   ;; reddens *because* the code got faster is measuring the wrong thing.
   ;;
   ;; Still the check most exposed to the header's cold/warm gap, though a narrower one at
   ;; this baseline: 5.70x under `--only` against 6.63x in place, the split being in the
   ;; denominator as it is everywhere.  Read a passing `--only` here as a cold reading and
   ;; nothing more.
   {:name      :negation-arbitration
    :claim     "8x the standing P/¬P dilemmas costs under 11x per assert — linear in the set, not a re-derivation of it each"
    :sizes     [100 800]
    :max-ratio 11.0
    :run       negation-arbitration}

   {:name      :negation-load
    :claim     "a negative fact with no positive twin costs the same at 2000 as at 250"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       negation-load}

   {:name      :feed-listener-scaling
    :claim     "an assert watched by a listener costs the same at 2000 as at 250 — per region, not per store"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       feed-listener-scaling}

   ;; The bound is the file's standing 2x for a *flat* claim, and it is set from the
   ;; claim rather than from a reading.  A teardown can only orphan a constant one of the
   ;; removed sentexes named, so the candidates are a property of what was removed and the
   ;; two readings here differ by the retraction's own cost and nothing else.  A
   ;; population term is the whole thing being gated, and a bound wide enough to admit one
   ;; would be a bound admitting it.
   ;;
   ;; The baseline is 32 for `clash-arbitration`'s reason.  A retraction has a fixed cost
   ;; of its own — the storage teardown, the settle, the feed event — and the small size
   ;; has to be one where that still dominates, or a baseline already carrying a hundred
   ;; NATs' worth of the per-NAT term divides it back out and compresses the spread the
   ;; bound has to separate.
   {:name      :retract-nat-scaling
    :claim     "retracting a fact that names no NAT is flat in the reified-NAT population it is not about"
    :sizes     [32 1024]
    :max-ratio 2.0
    :run       retract-nat-scaling}

   {:name      :columnar-fanout
    :claim     "an insert into the columnar trie is flat in the fan-out of the node it lands on"
    :sizes     [4000 64000]
    :max-ratio 2.0
    :run       columnar-fanout}

   {:name      :exception-roster-gate
    :claim     "exception-rule? is flat in how many rules carry an exception"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       exception-roster-gate}

   {:name      :overlay-selectivity
    :claim     "a fork's count-with-functor is flat in the size of the base posting it inherits"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       overlay-selectivity}

   {:name      :intersect-selectivity
    :claim     "narrowing a rare argument root against a hot one is flat in the hot posting's extent"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       intersect-selectivity}

   {:name      :arity-reach-trigger
    :claim     "a fact of a predicate whose arity is declared is flat in that predicate's extent"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       arity-reach-trigger}

   {:name      :plan-scaling
    :claim     "planning one fixed conjunction is flat in the size of the KB it is planned against"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       plan-scaling}

   ;; The bound is 4x rather than 2x because the vocabulary itself grows here — 8x the
   ;; sentexes is 2.8x the terms, and the report is entitled to that much.  What it
   ;; separates is 2.8x from the 8x a record scan reads, and 4x sits between them with
   ;; room on both sides.
   ;;
   ;; **Four of the census's seven readings**, and the claim says so.  This KB declares no
   ;; `arg`, `genlArg` or `interArg`, so the declarations reading walks an empty list
   ;; at both sizes and nothing here is a claim about it — the two checks below are.  It
   ;; stores no rule either, so the two rule-hygiene readings pair an empty set at both
   ;; sizes: their cost is the rule count and this workload holds it at zero.
   {:name      :quality-report-scaling
    :claim     "the rules, extents, chains and taxonomy readings of kb-quality grow with the vocabulary, not with what the KB stores"
    :sizes     [4000 32000]
    :max-ratio 4.0
    :run       quality-report-scaling}

   ;; **The fifth reading, first factor.**  Ω(declarations) is the floor — the census reads
   ;; each one — so 8x the declarations is at least 8x the walk, and the bound is a claim
   ;; about what sits above the floor.  Healthy it reads **7.56x and 7.71x** on full runs and 7.14x
   ;; alone, and the vocabulary is fixed at both sizes, so 97% of the reading is the walk
   ;; itself: the same KB with the declarations left out costs 0.051 ms against 1.756 at
   ;; n=250.  Below it, the form the arity table exists to replace — `checks/tabled-arity`
   ;; answered off the index rather than off the taxonomy, a walk of the argument-1 posting
   ;; these very declarations fill, so a census of n costs n² — reads **59.62x**,
   ;; implemented and measured on a full run rather than supposed.  15x is about twice the
   ;; healthy reading and under a third of the defective one, which is the slack the
   ;; arbitration bounds carry.
   {:name      :quality-declaration-census
    :claim     "the declarations census costs one arity reading per declaration, not one per declaration per declaration"
    :sizes     [250 2000]
    :max-ratio 15.0
    :run       quality-declaration-census}

   ;; **The fifth reading, second factor**, and the bound is read the same way.  The walk is
   ;; per super-predicate, so Ω(depth) is the floor here and 32x the hierarchy is at least
   ;; 32x — until the constant cost of the other four readings divides into it, which is
   ;; what puts a healthy reading under the span rather than over it: **22.78x, 24.26x and 26.11x** on
   ;; full runs and 20.29x alone, of which the declaration walk is nine parts in ten — the same KB with the
   ;; declarations left out costs 4.964 ms against 41.856 at n=256.  Below it, a
   ;; release asked of every super's own ancestry instead of every super — the square of the
   ;; depth per declaration — reads **74.75x** on a full run.  45x sits between them, and it is
   ;; placed differently from every other bound here: the honest floor is nearly the span, so
   ;; the healthy reading starts high and twice it is 52x, which is close enough to the
   ;; defect to be a bound that admits it on a bad run.  45x is the midpoint of the measured
   ;; pair instead — 1.7x above the worst healthy reading and 1.7x under the defective one.
   {:name      :quality-declaration-depth
    :claim     "the declarations census costs one arity reading per super-predicate, not one per super's own ancestry"
    :sizes     [8 256]
    :max-ratio 45.0
    :run       quality-declaration-depth}

   ;; The baseline is 64 for `clash-arbitration`'s reason: a retraction's own fixed cost
   ;; — the storage teardown, the settle, the feed event — has to still dominate at the
   ;; small size, or a baseline already carrying the whole-relation pass divides it back
   ;; out.  64 unrelated contexts is a graph such a pass crosses in well under that.
   {:name      :retract-context-cycle-scaling
    :claim     "retracting an edge of a context cycle is flat in the context graph it is not about"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       retract-context-cycle-scaling}

   ;; The baseline is 32 for `retract-nat-scaling`'s reason, which is `clash-arbitration`'s:
   ;; a retraction has a fixed cost of its own — the storage teardown, the settle, the feed
   ;; event — and the small size has to be one where that still dominates, or a baseline
   ;; already carrying a hundred merges' worth of the per-merge term divides it back out.
   ;;
   ;; **This is the third bound in the file that is not *flat*, and for the same kind of
   ;; reason as the other two.**  A settle with any supersession in play reconciles the
   ;; taxonomy caches against a moved set that includes every superseded handle, old and
   ;; new, because a supersession flip leaves no relabel to record it
   ;; (`settle/settle-finish`).  So Ω(merged) per settle is here by construction and is not
   ;; what this check is about; what it is about is whether the **reconcile of the
   ;; superseded set itself** re-examines every displaced spelling, which costs a record
   ;; fetch, a rewrite through the closure and a store probe apiece.
   ;; **The bound is read off a FULL run.**  This check's large reading barely moves
   ;; between `--only` and the gate (0.733 against 0.747 ms), while its *baseline* halves
   ;; (0.129 against 0.067), because by the twentieth check the JVM is warm and this
   ;; check's baseline is dominated by the n-independent constant.  The ratio inflates
   ;; from a faster denominator and nothing else: 5.66x alone against 11.22x in place,
   ;; same tree, same commit.  It bites here rather than on a flat check because
   ;; Ω(merged) leaves a real per-merge term in the numerator for the warm baseline to
   ;; divide into.  A bound read off `--only` fails every full run, so this one is not:
   ;; it is measured in a full run both ways rather than tuned until green — **11.22x**
   ;; narrowed against **32.12x** with the reconcile re-examining every standing entry,
   ;; and the absolute large readings say the same without a ratio at all — 0.747 ms/op
   ;; against 13.742.  18x sits between them.  Healthy full runs read 10.49-14.42x, so
   ;; the headroom on a loaded box is nearer 1.25x than the spread above suggests; this
   ;; check and the two taxonomy-edge ones are the file's tightest, and `--tolerance`
   ;; is the answer to a red run on a busy machine rather than a wider bound here.
   {:name      :retract-merge-scaling
    :claim     "retracting a fact naming no merged term costs under 18x per 32x the standing merges — bookkeeping, not a re-examination each"
    :sizes     [32 1024]
    :max-ratio 18.0
    :run       retract-merge-scaling}

   ;; Flat at the file's standing 2x, and the claim is exact: an edge that reaches no
   ;; exception must cost the same whether the KB's excepted rule has fired 32 times or
   ;; 1024.  The baseline is small for the usual reason — at 32 firings the per-firing
   ;; term has barely started, so it is not sitting in the denominator.
   {:name      :genl-edge-negation-recheck
    :claim     "a genl edge is flat in the firing history of a negated exception it cannot reach"
    :sizes     [32 1024]
    :max-ratio 2.0
    :run       genl-edge-negation-recheck}

   ;; The two taxonomy-edge checks, and their bounds are `clash-arbitration`'s reasoning
   ;; applied to the workload that file could not see: Ω(standing) is the honest floor —
   ;; a settle republishes the whole standing set whatever moved it — and what the bound
   ;; separates is *bookkeeping per standing pair* from *a re-derivation per standing
   ;; pair*.
   ;;
   ;; The baseline is **8**, and that is the header's own advice taken twice.  At 25 the
   ;; baseline of the `genlCx` check already carried 25 pairs' worth of the
   ;; re-derivation being measured, which divided out and left a defective engine reading
   ;; between 10.9x and 21.2x depending on which way the small reading bounced — a gate
   ;; that would have passed the very shape it exists to catch, roughly one run in four.
   ;; Eight is a size at which the re-derivation has barely started.
   ;;
   ;; **These two bounds are set from a full run, not from an isolated one, and the gap is
   ;; large enough to be stated here.**  Everything here is Ω(standing) by construction,
   ;; so the reading is `a + b·n` and the *ratio* is decided by how big the fixed term `a`
   ;; is at the baseline — which is JIT warmth, and by the twentieth check of a run the
   ;; JVM is much warmer than it is on `--only`.  The large reading barely moves (it is
   ;; real per-pair work, which no amount of warmth removes) and the small one drops by a
   ;; third, so the ratio climbs: the `genl` check reads 9.8-13.2x alone and 17.3-22.7x in
   ;; place, the `genlCx` one 9.1-9.8x alone and 15.8-21.4x in place.  Bounds read off
   ;; an `--only` run would fail every full one, which is the mirror image of the warming
   ;; bias `measure` describes and lands on the same rule: judge a check where it runs.
   ;;
   ;; Measured at 100x the standing set, both engines, full runs: a `genl` edge reads at
   ;; worst 22.7x with the carry weighed per pair and 106.6x with it retired on the
   ;; relation's generation; a `genlCx` edge reads 21.4x against 65.6x.  So each
   ;; bound sits half again above the worst healthy reading and at a third to a half of
   ;; the defective one.
   {:name      :taxonomy-edge-arbitration
    :claim     "a genl edge separating nothing costs under 35x per write at 100x the standing clashes"
    :sizes     [8 800]
    :max-ratio 35.0
    :run       taxonomy-edge-arbitration}

   {:name      :context-edge-arbitration
    :claim     "a genlCx edge reaching nothing costs under 32x per write at 100x the standing P/¬P dilemmas"
    :sizes     [8 800]
    :max-ratio 32.0
    :run       context-edge-arbitration}

   ;; **32x the subtree, and both ends of the bound are measured.**  Above: a linear sweep
   ;; reads **16.49x and 19.90x** on full runs, the warm baseline the namespace docstring
   ;; describes putting them above what the same pair reads alone.  Below: the sweep's reach re-derived per predicate
   ;; instead of once for the pass — the subtree expanded and cardinality-read inside the
   ;; per-fact check — reads **133.48x** on a full run, implemented against
   ;; this workload rather than supposed for it.  45x is 2.3x the healthy reading and a
   ;; third of the defective one, which is the slack the arbitration bounds carry.
   ;;
   ;; The span is 32x rather than 16x for the reason every other Ω(n) check here takes 32x:
   ;; a quadratic separates from a linear by the span, so a narrow one is a narrow gap to
   ;; put a bound in.  Not `flat`: the facts a binding convicts are the subtree's facts, and
   ;; a bound that demanded flatness would demand the report miss them.
   ;;
   ;; Read with the docstring's last paragraph: `special/subsumption-seeds` walks the same
   ;; subtree on the same edge and owns the larger half of the reading, so what this ratio
   ;; separates is linear from quadratic and not one pass from the other.
   {:name      :arity-reach-under-subtree
    :claim     "a genl edge binding an arity over 32x the subtree costs under 45x per write — the sweep is linear in the facts it must examine, not in the square of them"
    :sizes     [8 256]
    :max-ratio 45.0
    :run       arity-reach-under-subtree}

   ;; **The one bound in this file that records a cost rather than gating one**, and it is
   ;; worth reading before the number.  A settle expands every root it was handed into that
   ;; root's spec subtree, and a deferred batch of taxonomy edges hands it one root per
   ;; edge — so a batch whose edges form a chain pays the sum of the subtrees, which is the
   ;; square of the batch.  Measured on the shipped tree, one settle over a chain: 0.336 ms
   ;; at 32 edges, 4.056 at 128, 60.559 at 512, 252.139 at 1,024 — four times the cost for
   ;; twice the edges, at every step.  The same batch on a KB declaring no arity costs
   ;; 0.374 ms at 1,024, which is what the expansion is worth and what a fix would return.
   ;;
   ;; **That fix landed, and this is re-pinned at the floor it predicted.**  `tax/specs-of-all`
   ;; seeds one traversal with every root, so the walk is the union rather than the sum of
   ;; the parts: 512 chained edges went from 60.559 ms to **1.012**, and the reading from
   ;; 59.49x to **7.50x and 11.34x** on full runs (3.78x alone).  The n=512 end is the
   ;; steady one across all three — 1.012, 1.095, 0.999 — and the spread is the n=64
   ;; baseline, which is small enough to be mostly JIT warmth.
   ;;
   ;; So the two ends are: **7.50x and 11.34x healthy**, against **63.58x** for the
   ;; per-root expansion this replaced and **46.99x** for the half-fix that unioned the
   ;; subtrees before counting them but still expanded each one — both measured, the
   ;; second because it looked like the whole answer and was worth 15%.  25.0 sits above
   ;; twice the worse healthy reading and under half the nearer defect.  The floor with
   ;; the pass off is 2.13x, so what is left to regress is the constant, not the shape.
   ;;
   ;; The baseline is 64 for `clash-arbitration`'s reason: the settle has a fixed cost of
   ;; its own, and the small size has to be one where that still dominates the term being
   ;; measured.
   {:name      :arity-reach-batch-roots
    :claim     "one settle over 8x the deferred genl edges costs under 25x — the roots of a batch are expanded together, so a chain costs its union and not its sum"
    :sizes     [64 512]
    :max-ratio 25.0
    :run       arity-reach-batch-roots}

   ;; **Flat, and calibrated from both ends.**  Healthy it reads **0.99x and 1.00x** on full runs: the edge's two ends are sized off an O(1) count apiece and the empty one
   ;; is walked, so the facts behind the other end are never touched.  The shape this exists
   ;; to catch — the end below always taken, which is the natural way to write it and
   ;; answers exactly the same thing — reads **6.42x** on a full run, measured by forcing the choice
   ;; rather than by supposing a number for it.  The bound is the flat claim's own 2.0x, an
   ;; order under the defect.
   ;;
   ;; The sizes are `constraint-exposure-context-edge`'s, and the defect has to be visible
   ;; at both: 2,000 facts is under `*exposure-instance-budget*`, so a pass walking the
   ;; wrong end here is measured walking it rather than being capped part way.
   {:name      :arity-context-edge-side
    :claim     "a genlCx edge's arity reach walks its smaller end — flat in what the larger end holds"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       arity-context-edge-side}

   ;; **Flat past the cap, and the cap is bound to 100 to reach it** —
   ;; `constraint-exposure-context-edge`'s reading of the same budget, on the other pass
   ;; that spends it.  Healthy 0.76x and 0.96x on full runs, 0.69x alone; the budget never
   ;; consulted reads **7.58x** on a full run (7.25x alone, 6.70 ms against 48.59) — the sweep
   ;; tracking the subtree's extent instead of its own bound.
   ;;
   ;; Below the cap the sweep is proportional to what it examines and deliberately so —
   ;; that is `arity-reach-under-subtree` two rows up, and this check is the claim that the
   ;; cap is a cap.
   {:name      :arity-reach-budget-cap
    :claim     "past the instance cap, 8x the facts behind an arity binding costs the same"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       arity-reach-budget-cap}

   ;; **The gate, and the sweep it gates, as two rows.**  A `functional` mark descends a
   ;; `genl` edge to the subtree below it, so the edge implicates that subtree's facts;
   ;; `genl` is the commonest edge an ontology writes, so the arm is gated on a mark being
   ;; at or above the edge's own `sub`.
   ;;
   ;; Gated: the gate removed — opened on this workload's own predicate, implemented and
   ;; measured rather than supposed — reads **4.33x** on a full run.  Healthy is flat, and
   ;; **the bound is 2.5x rather than the flat claim's 2.0x because of the spread rather
   ;; than the claim**: the readings here are a few tenths of a millisecond, which is where
   ;; run-to-run warmth moves a ratio more than the cost does.  Three isolated runs land
   ;; between 0.83x and 0.90x and two full runs read 1.09x apiece, and on a busier box the same tree
   ;; has read 1.85x — the difference being a baseline the gate measures warm.  2.5x sits above that spread and
   ;; at 1.6x under the defect; `--tolerance` is the answer to a red run on a busy box, and
   ;; the runner's re-measure already gives a bounced baseline a second look.
   {:name      :constraint-genl-edge-gate
    :claim     "a genl edge under no functional or asymmetric mark is flat in the subtree it does not walk"
    :sizes     [250 2000]
    :max-ratio 2.5
    :run       (constraint-genl-edge false 4096)}

   ;; ...and the sweep the gate lets through, which is budgeted rather than free: healthy
   ;; 0.98x and 1.03x on full runs, 0.76x alone, with the cap at 100, against **7.01x** at the shipped
   ;; 4,096 where 2,000 facts
   ;; sit under the cap and the reading is the subtree instead — the same reading
   ;; `constraint-exposure-context-edge` records for its own budget, and the same argument.
   ;; The two rows fail for opposite reasons: this one if the sweep stops being bounded,
   ;; the one above it if the sweep stops being gated.  The bound is the flat claim's 2.0x,
   ;; which this one can carry: the capped sweep is a constant few tenths of a millisecond
   ;; on top of the flip, and a reading with more in it bounces less.
   {:name      :constraint-genl-mark-descent
    :claim     "past the instance cap, 8x the facts a descending mark reaches costs the same"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       (constraint-genl-edge true 100)}

   ;; **The bound is 175x, and here is what it was read off.**  Two healthy full-run
   ;; readings, 85.4x and 80.9x, against a floor near 66x — so the honest reading sits
   ;; about 1.25x above the floor and the spread between runs is a few percent.  Below it,
   ;; the form the claim rules out: `contradictions` filtering the standing set by cross
   ;; product before ranking it reads **937.8x**, which is the square arriving exactly
   ;; where the paragraph below says it does.  175x is 2.05x above the worse healthy
   ;; reading and 5.4x below the defective one, which is the same slack the arbitration
   ;; bounds beside it carry.  Both numbers come off a **full** run rather than an
   ;; `--only` one, for the reason the namespace docstring gives.
   ;;
   ;; That the defective shape read 937.8x is also why a placeholder is not a gate: it
   ;; passed, silently, under the 1000x that meant "nobody has measured this".
   ;;
   ;; The read path of the standing set, and one of the two workloads here whose reading
   ;; grows with n by construction (`quality-report-scaling` is the other): a reading
   ;; returns every standing pair, so it costs the answer's own size and 32x the
   ;; dilemmas is at least 32x the reading.  Ordering them adds the
   ;; log term, which puts the honest floor between these two sizes near 66x rather than
   ;; 32x — so the bound is a claim about what sits **above** the floor.  A read that
   ;; re-derives the pairing, filters the standing set by cross product, or rebuilds each
   ;; report from the store per call is super-linear, and separates from the floor by the
   ;; square rather than by a constant.
   ;;
   ;; The sizes are `negation-arbitration`'s over the identical KB shape, so the two are
   ;; the write cost and the read cost of one standing set and can be quoted against each
   ;; other — the comparison the ordering's placement rests on.  The header's advice about
   ;; a small baseline lands differently here and is still followed: what a large baseline
   ;; would divide out of this ratio is not a per-pair term (the per-pair term is the whole
   ;; reading) but the fixed cost of the call, and at 25 pairs that is already small.
   ;;
   ;; **What a ratio cannot see here**, since a green run should not be read as more than
   ;; it is: the `::order` key `settle/record-clashes!` attaches per report buys a
   ;; *constant* factor — one metadata read per comparison in place of four `pr-str`s —
   ;; and both shapes are n log n, so this is blind to losing it.  And the regression that
   ;; puts the ordering back on the settle path is a **write**-path cost: it lands on
   ;; `negation-arbitration` and not here.
   {:name      :standing-clash-reading
    :claim     "a reading of the standing dilemmas costs what it returns — an ordering of the standing set, not a re-derivation of it"
    :sizes     [25 800]
    :max-ratio 175.0
    :run       standing-clash-reading}

   ;; **Flat, and calibrated from both ends** as the header requires. Healthy it reads
   ;; **0.91x and 0.90x** on full runs (0.74x under `--only`): the answer set is one fact
   ;; at both sizes and a roster lookup does not care how much the roster holds. The shape
   ;; this exists to catch — the filter re-deriving the hidden set per call, a walk over
   ;; every stored `except` — reads **27.33x**, measured by running this check against a
   ;; tree that has it rather than by supposing a number for it.
   ;;
   ;; The bound is the flat claim's own 2.0x, which is where the header puts a cost that
   ;; should not move with n at all, and it sits an order of magnitude under the defect
   ;; and twice the healthy spread. The defect's reading is an `--only` one and so if
   ;; anything understates it: a full run's warmer baseline divides a smaller number into
   ;; the same large one.
   ;;
   ;; The small size is 8 rather than 25 for the header's reason: at 25 excepts a walk is
   ;; already carrying enough per-except cost to divide some of itself out of the ratio.
   {:name      :visibility-reading
    :claim     "a scoped read costs what it returns, not what the KB hides"
    :sizes     [8 1024]
    :max-ratio 2.0
    :run       visibility-reading}

   ;; The reader fan a `genlCx` edge sweeps.  Flat by construction: the bystanders read
   ;; the candidates' branch and sit under no `sub`, so the edge changes no ancestor set
   ;; of theirs and the widened set is the same size at both n.  The shape this exists to
   ;; catch is the one that shipped — the sweep taking `context-down` of each candidate's
   ;; own storage context rather than of `sub`, which put every bystander in the fan at
   ;; one derivation per candidate apiece.
   ;;
   ;; **Calibrated from both ends**, at the two readings that bracket it.  Healthy it
   ;; reads **1.02x** under `--only` (2.012 ms/op against 2.048) and **1.52x** on a full
   ;; run (1.370 against 2.088) — the header's warmer-baseline gap, which shows here
   ;; because the small size's own reading is small.  Against the defect, measured on a
   ;; worktree at the parent commit, it reads **15.51x** (2.996 ms/op against 46.456).  So
   ;; 3.0 is twice the healthy spread and five times under the defect, which is
   ;; `visibility-reading`'s rule for the same shape.  A bound at 2.0 would sit 24% over
   ;; a full run's healthy reading, which is the margin `inherit-reach-memo` lives on and
   ;; the reason it is the one check here that flakes.
   ;;
   ;; `genlcx_sweep_cost_test` counts the same fan in the suite, exactly and with no
   ;; tolerance, and `genlcx_sweep_test` holds what the sweep must still derive.
   {:name      :genlcx-edge-reader-fan
    :claim     "a genlCx edge costs the readers it widened, not every reader below its candidates"
    :sizes     [8 512]
    :max-ratio 3.0
    :run       genlcx-edge-reader-fan}

   ;; **The only check here that writes to a disk**, and the first thing in this file to
   ;; measure the durable stores at all.  Flat, and calibrated from both ends.  Healthy it
   ;; reads **1.06x** on a full run (0.113 ms/op against 0.120) and 0.94x, 0.97x, 0.82x,
   ;; 0.87x and 1.00x across five isolated ones: the per-record cost is fixed by
   ;; construction — one log frame and one idx slot per record, one packed append for a
   ;; whole WAL batch — so nothing about it is entitled to grow with what the log already
   ;; holds, and the header's warning about a warmer baseline in the full run barely
   ;; applies to a reading with no n-dependent term in it.  Below it, the form the check
   ;; exists to catch: the index WAL logging the resulting **value** instead of the op, so
   ;; an `:add-to-set` frame carries the grown set rather than the one added member and a
   ;; linear load writes a quadratic number of bytes.  Implemented against this very
   ;; workload rather than supposed for it, it reads **6.38x** (0.442 ms/op against
   ;; 2.816).  2.0x is the flat claim's own bound, at twice the worst healthy reading and
   ;; a third of the defect.
   ;;
   ;; **What the span does not separate**, since the readings are tenths of a millisecond
   ;; and a green run should not be read as more than it is: an append that finds the
   ;; log's end by walking the frame-length chain instead of asking the file its length
   ;; reads **1.77x** over this 8x span — a real linear term, but one whose per-record
   ;; share at 8,000 frames is still small next to the frame write, so it passes.  The
   ;; span is 8x rather than 32x because 32,000 durable asserts is half a minute of the
   ;; gate's five, which is a large price for widening one bound.
   ;;
   ;; The counted companion is `test/vaelii/disk_write_cost_test.clj`, and it is the half
   ;; that holds the *constant* — how many file operations a record costs — for the reason
   ;; the header gives about `assert_cost_test`: the syscall packing this path was built
   ;; for is a constant, and a constant divides out of every ratio in this file.
   {:name      :durable-fact-append
    :claim     "a fact reaching the durable log is flat in what the log already holds — the index WAL logs the op, not the grown value"
    :sizes     [1000 8000]
    :max-ratio 2.0
    :run       durable-fact-append}

   ;; The pair of claims docs/qcn.md's cost section opens with, and the one this file can
   ;; hold: **the read is not the pass**.  The pass is superquadratic and says so; what
   ;; residency promises is that a *repeat* consultation costs what the answer costs and
   ;; not what the KB holds.  8x the stored extent of the calculus predicate, none of it
   ;; visible from the asking context, and the reading may not follow it.
   {:name      :qcn-network-residency
    :claim     "a repeated qualitative consultation is flat in the stored extent of the calculus it is not about"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       qcn-network-residency}

   ;; Not a flat claim, and the bound says which claim it is instead.  `undercut?` is a
   ;; cross-product over the claims however the reaches are answered, so the comparing is
   ;; quadratic in n whatever happens — what the memo makes linear is the *walking*, and 8x
   ;; the claims at 64x the cost is what a lost memo reads.  12x sits between the two, the
   ;; same reasoning `membership-under-depth` picks its bound by.
   {:name      :inherit-reach-memo
    :claim     "8x the claims reaching one term costs under 12x per ask — one reach walk per question, not one per pair of claims"
    :sizes     [8 64]
    :max-ratio 12.0
    :run       inherit-reach-memo}

   ;; The metric twin of the qualitative residency check above, and the bound is calibrated
   ;; the way `membership-under-depth` and `inherit-reach-memo` are: from both ends, on full
   ;; runs.  A closure bounds every pair of instants, so an arriving constraint is quadratic
   ;; in the instant count whatever route it takes and no memo makes it flat — what the gate
   ;; defends is that the route is a **relaxation** and not a fresh cubic pass.  At 8x the
   ;; instants it reads 12.6x-13.4x over three full runs, and 99.5x with the same check
   ;; driving `stp/close-state` instead, which is the form the bound exists to catch.
   ;; 35x sits between, and the absolute readings say it louder: 1.9 ms an arrival
   ;; against 101 ms.
   {:name      :metric-closure-warm-start
    :claim     "8x the instants costs under 35x per arriving constraint — the closure is relaxed into, not run again"
    :sizes     [50 400]
    :max-ratio 35.0
    :run       metric-closure-warm-start}])

;; ---- the runner ---------------------------------------------------------

(def ^:private quick-slack
  "How much `--quick` widens each bound.  One attempt over the real pair is noisier
  than the gate's re-measured best-of-two, so the bound gives that noise room — a
  borderline reading passes where the full gate would look twice, and a genuine
  regression still fails."
  1.5)

(defn- run-check
  "Measure one check at both sizes and judge the growth.  A check over its bound is
  measured again from scratch and the *better* ratio stands: a GC pause or a scheduler
  hiccup landing in one window is not a regression, and an algorithmic one survives being
  looked at twice."
  [{:keys [sizes max-ratio run]} tolerance quick?]
  (let [[small large] sizes
        ;; quick widens the bound instead of shrinking the pair: one attempt over the
        ;; real sizes is a coarse verdict, where measuring one size twice is six runs
        ;; and no possible failure — a gate that cannot fail is decoration
        bound   (* (double max-ratio) (double tolerance) (if quick? quick-slack 1.0))
        ;; the *large* size is what both warm to: it is the one whose reading the bound
        ;; is a claim about, so it is the one that must not be measured warmer than its
        ;; baseline was
        attempt (fn [] (let [a (measure run small large)
                             b (measure run large large)]
                         {:small a :large b :ratio (/ b (max a 1.0))}))
        first-try (attempt)
        best      (if (or quick? (<= (:ratio first-try) bound))
                    first-try
                    (min-key :ratio first-try (attempt)))]
    (assoc best
           :bound  bound
           :sizes  [small large]
           :status (cond (< (:small best) noise-floor-ns) :noise
                         (<= (:ratio best) bound)         :pass
                         :else                            :fail))))

(defn- report [{:keys [name claim]} {:keys [small large ratio bound sizes status]}]
  (let [[s l] sizes]
    (println (format "  %-20s %s" (clojure.core/name name)
                     (case status
                       :pass  "PASS"
                       :fail  "FAIL"
                       :noise "noise — below the gating floor, not judged")))
    (println (format "    %s" claim))
    (println (format "    n=%-6d %8.3f ms/op        n=%-6d %8.3f ms/op"
                     s (/ small 1e6) l (/ large 1e6)))
    (when-not (= :noise status)
      (println (format "    growth %.2fx  (bound %.2fx)" ratio bound)))
    (println)))

(defn- usage-exit [msg]
  (binding [*out* *err*]
    (println msg)
    (println "usage: lein perf [--only <name>] [--tolerance <x>] [--quick]"))
  (System/exit 2))

(defn- parse-args [args]
  ;; refused, not guessed: `--only` with no value would run the WHOLE gate while
  ;; reading as a single-check run, a dropped unknown flag gates at the default
  ;; tolerance (`--tolerence 1.5` at 1.0), and a bare `--tolerance` NPEs — which
  ;; gate.sh reports exactly like a regression
  (loop [m {:tolerance 1.0 :quick? false :only nil} [a & more] args]
    (case a
      nil          m
      "--quick"    (recur (assoc m :quick? true) more)
      "--only"     (if-some [v (first more)]
                     (recur (assoc m :only (keyword v)) (rest more))
                     (usage-exit "--only needs a check name"))
      "--tolerance" (if-some [v (first more)]
                      (let [x (try (Double/parseDouble v)
                                   (catch NumberFormatException _
                                     (usage-exit (str "--tolerance: not a number: " v))))]
                        (recur (assoc m :tolerance x) (rest more)))
                      (usage-exit "--tolerance needs a number"))
      (usage-exit (str "unknown flag: " a)))))

(defn -main [& args]
  (let [{:keys [tolerance quick? only]} (parse-args args)
        selected (cond->> checks only (filter #(= only (:name %))))]
    (when (empty? selected)
      (println "no such check:" only "— have:" (mapv :name checks))
      (System/exit 2))
    (println (format "\nvaelii performance gate — %d check(s), tolerance %.2fx%s\n"
                     (count selected) (double tolerance) (if quick? ", quick" "")))
    (let [total   (count selected)
          ;; Every verdict is reported together at the end (below), so the run itself
          ;; emits nothing per check — a `perf-progress k/total name` marker on *err*
          ;; as each finishes gives `lein gate` something to poll into a live bar
          ;; (scripts/gate.sh) without touching the clean stdout verdict stream.
          results (doall
                   (map-indexed
                    (fn [i c]
                      (let [r (run-check c tolerance quick?)]
                        (binding [*out* *err*]
                          (println (format "perf-progress %d/%d %s"
                                           (inc i) total (name (:name c))))
                          (flush))
                        [c r]))
                    selected))]
      (doseq [[c r] results] (report c r))
      (let [failed (filter (fn [[_ r]] (= :fail (:status r))) results)]
        (if (seq failed)
          (do (println (format "%d of %d checks REGRESSED: %s"
                               (count failed) (count results)
                               (mapv (comp :name first) failed)))
              (shutdown-agents)
              (System/exit 1))
          (let [noisy (filterv (fn [[_ r]] (= :noise (:status r))) results)]
            ;; the floor's whole point: a check too fast to gate says so instead of
            ;; turning into a green light nobody notices has stopped meaning anything
            (println (format "%d check(s) ok%s"
                             (- (count results) (count noisy))
                             (if (seq noisy)
                               (format ", %d below the gating floor — not judged: %s"
                                       (count noisy) (mapv (comp :name first) noisy))
                               "")))
            (shutdown-agents)
            (System/exit 0)))))))
