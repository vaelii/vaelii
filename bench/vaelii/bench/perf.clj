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
  again, the better of the two runs standing — a GC pause landing in one
  window is not a regression, and a real one survives a second look.

  **A ratio is only as good as its baseline**, and both ways of getting that wrong have
  already happened here.  Warming the JVM proportionally to `n` gave the large size a
  head start and made an n-*independent* check read 0.68x (see `warm!`).  And a
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
  runs — `retract-merge-scaling` and `taxonomy-edge-arbitration` read their bounds off
  full runs for this reason.

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
  refusing: healthy it reads 17.6x-81.8x on full runs from 2026-10-01 to 2026-10-10, and
  with the read filtering the standing set by cross product it reads 937.8x.  A placeholder of 1000x —
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
  holds the *constant* — and a change to the write path wants both.  A constant the index
  count cannot see either — a slower operation that reads no more — is
  `lein perf-ab <base-rev>`'s: `vaelii.bench.ab`'s probes on both revisions, in absolute
  time.

  Run: `lein perf [--only <name>[,<name>…]] [--tolerance <x>] [--quick] | --list`

    --only       run the named checks, comma-separated (the `:name` below, without the
                 colon), in roster order whatever the order given.  A name in `groups`
                 runs every check of that group
    --list       print each check's group, name and claim, and measure nothing
    --tolerance  multiply every bound by this — 1.5 on a noisy box, 1.0 in anger
    --quick      one attempt over the real pair at a 1.5x-widened bound — a coarse
                 verdict for a pre-commit read, still a verdict

  Exit status is 0 when every check passes, 1 when any fails, which is what makes it
  usable from a hook or a workflow."
  (:require [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.asp.solve-context :as sc]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.dense-roots :as dense-roots]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.except :as exc]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.space :as space]
            [vaelii.impl.special :as special]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [taoensso.nippy :as nippy]))

;; ---- measurement --------------------------------------------------------

(def ^:private noise-floor-ns
  "Below this a per-operation reading is mostly timer and scheduler jitter, and the ratio
  of two such readings says nothing.  A check that lands here is reported and skipped
  rather than passed, so a check that becomes too fast to gate says so instead of turning
  into a green light nobody notices has stopped meaning anything."
  20000)                                                    ; 20µs

(def ^:private ^:dynamic *backend*
  "The `:backend` `fresh-kb` opens: `:memory`, or another in-memory pairing a check binds."
  :memory)

(defn- fresh-kb
  "An empty KB on its own space, so one check cannot leave state in another's."
  []
  (let [k (v/open-kb {:space 9 :recover? false :backend *backend*})]
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

(def ^:private warm-runs
  "How many times `warm!` runs a check at its large size before either size is read."
  2)

(defn- warm!
  "Run `f` at the large size `n` `warm-runs` times, readings discarded.

  **Both sizes are read after the same warming, to the large size**, and that is the
  whole point.  Warming proportionally to `n` — a fifth of the run, say — hands the large
  size a JVM that has JIT-compiled the very code being timed while the small size is
  still climbing to it, and the reading comes back *faster at the larger size for no
  reason but that*.  It is not a subtle effect: `arg-root-retrieval` does work that is
  n-independent by construction, and it measured 0.68x that way.

  A gate is exactly where that matters, since the bias flatters the large size and a
  ratio bound is a claim about the large size.  A regression would be measured against a
  baseline that had been quietly discounted.  `run-check` warms once and reads the small
  size first, so the large reading is never warmer than the small one by more than one
  small run."
  [f n]
  (dotimes [_ warm-runs] (f n)))

(defn- measure
  "Per-operation nanoseconds for `f` at size `n`: the tail mean of one run after a GC.
  The caller warms first (`warm!`)."
  ^double [f n]
  (System/gc)
  (tail-mean (f n)))

(defmacro ^:private nanos [& body]
  `(let [t# (System/nanoTime)] ~@body (- (System/nanoTime) t#)))

;; ---- the checks ---------------------------------------------------------
;;
;; Each is `{:name :group :claim :sizes [small large] :max-ratio :run}`, where `:run`
;; takes a size and returns per-operation nanosecond readings, and `:group` is a key of
;; `groups`.  `:claim` is what the check is
;; for; it prints beside the verdict, so a failure says which promise broke rather than
;; only which number moved.
;;
;; A check with no `:max-ratio` is a **baseline**: measured once at both sizes, printed
;; with its growth, and never judged.  It is the before-reading for a cost whose curve
;; still grows by design, and the change that flattens the curve gives it a bound read
;; off both ends, as the header says.  A baseline cannot fail the run, and its report
;; says so in place of PASS.
;;
;; A check with `:unmet true` states a bound the engine does not meet.  It is measured
;; once and judged: a reading over the bound reports UNMET and does not fail the run, and
;; a reading within it reports PASS beside the mark.  Its comment gives the reading the
;; engine takes.

(defn- clash-arbitration
  "n individuals each holding two separated types, so the KB carries n standing dilemmas,
  and an assert settles beside them.  The settle journals the clash members that entered
  or left and reads none of the n.

  The discovery it gates is the same one the derivation path runs, so the entry point
  and a rule firing pay the same cost here."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(disjoint pa_t pb_t) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)
           :let [x (symbol (str "PX" i))]]
       (do (v/assert kb (list 'pa_t x) 'CxPerf {})
           (nanos (v/assert kb (list 'pb_t x) 'CxPerf {})))))))

(defn- constraint-exposure-shared-arg
  "n facts of a declared-`asymmetric` predicate that all share argument 1.

  **A declared property opens the tuple-mark candidates.**  This declares `asymmetric`,
  so each assert reads the converse its own arguments name (`decide/note-candidate!`).

  The shared argument is what makes it a claim rather than a formality: `PA`'s posting
  grows by one per assert, so a pass that walks it per assert is O(n) each and O(n²) over
  the load, and the reading tracks the KB rather than the region. One context throughout,
  so no pair is ever visible from anywhere and nothing is decided — this measures the
  cost of *deciding that*, which is the cost every assert on such a KB pays.

  **The argument-1 posting is predicate-agnostic**, which is what makes the shape general
  rather than contrived: a read of it returns every sentex holding the term at argument 1
  and the functor filter runs after. So the risk is a heavily-used *individual* and not
  only a wide slot — a term at argument 1 of ten thousand facts of other predicates costs
  the same walk. This check drives it with one predicate because that is the shortest
  load that grows the posting; the narrowing it guards (`decide/note-candidate!` reads
  the one converse the tuple's arguments name) is what keeps either shape flat."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(asymmetric plarger) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'plarger 'PA (symbol (str "PL" i)))
                        'CxPerf {}))))))

(defn- per-reading-vantages
  "A cross-context membership pair whose separation is declared where the members'
  maximal common descendant cannot see it, under n contexts below that maximum.

  ```
  CxPA  (plt_a x)     CxPB  (plt_b x)     CxPDecl  (disjoint plt_a plt_b)
  CxPW sees CxPA and CxPB, and n contexts CxPL0 … see CxPW
   └─ CxPV sees CxPW and CxPDecl
  ```

  `CxPW` reads no separation, and `CxPV` does: each reader reads the separation over its
  own ancestor set (`membership/term-nogoods`).  **The claim is that an assert reads none of
  the n contexts below `CxPW`.**  Each timed assert is the second membership of a fresh
  term, so every one forms a pair, and the lattice is the only thing n moves.

  The maxima themselves are the other half of it: `CxPA` and `CxPB` see neither the other,
  so `tax/maximal-common-descendant-contexts` answers from its general path, which walks
  down from a member rather than filtering every common descendant."
  [n]
  (let [kb (fresh-kb)]
    (doseq [[k up] '[[CxPA CxUniverse] [CxPB CxUniverse] [CxPDecl CxUniverse]
                     [CxPW CxPA] [CxPW CxPB] [CxPV CxPW] [CxPV CxPDecl]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse {:strength :monotonic}))
    (v/assert kb '(disjoint plt_a plt_b) 'CxPDecl {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxPL" i)) 'CxPW) 'CxUniverse
                  {:strength :monotonic})))
    (doall
     (for [i (range 60)
           :let [x (symbol (str "PLX" i))]]
       (do (v/assert kb (list 'plt_a x) 'CxPA {})
           (nanos (v/assert kb (list 'plt_b x) 'CxPB {})))))))

(defn- chain-join
  "The closing step of an `anti_transitive` chain split across three contexts, beside n
  open chains split the same way.

  ```
  CxPA  (pnear a b)     CxPB  (pnear b c)     CxPC  (pnear a c)
  CxPAB, CxPBC and CxPAC each see two of them
   └─ CxPW sees all three
  ```

  The closing step reads the steps sharing an argument with it (`tuple/found-for`), and
  `CxPW`, which sees all three, decides the chain.  The open chains name terms of their
  own and share none with a timed chain, so the read reaches no posting n grows.  60 chains are closed and timed at
  either size, so the standing decisions are the same 60 at both."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (doseq [[k up] '[[CxPA CxUniverse] [CxPB CxUniverse] [CxPC CxUniverse]
                     [CxPAB CxPA] [CxPAB CxPB] [CxPBC CxPB] [CxPBC CxPC]
                     [CxPAC CxPA] [CxPAC CxPC]
                     [CxPW CxPAB] [CxPW CxPBC] [CxPW CxPAC]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse m))
    (v/assert kb '(binary_predicate pnear) 'CxUniverse m)
    (v/assert kb '(anti_transitive pnear) 'CxUniverse m)
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pnear (symbol (str "POA" i)) (symbol (str "POB" i))) 'CxPA m)
        (v/assert kb (list 'pnear (symbol (str "POB" i)) (symbol (str "POC" i))) 'CxPB m)))
    (doall
     (for [i (range 60)
           :let [a (symbol (str "PNA" i)) b (symbol (str "PNB" i)) c (symbol (str "PNC" i))]]
       (do (v/assert kb (list 'pnear a b) 'CxPA m)
           (v/assert kb (list 'pnear b c) 'CxPB m)
           (nanos (v/assert kb (list 'pnear a c) 'CxPC {})))))))

(defn- membership-read-under-busy-term
  "A type membership checked about a term that is already argument 1 of n facts of an
  unrelated binary predicate, on a KB that declares one separation.

  **The retrieval every definitional check bottoms out on.**  `kb/types-of` answers what
  types a term holds, and the disjointness arm asks it of the arriving sentence's
  argument on every membership.  The argument root cannot narrow to the memberships —
  `(T x)` and `(P x y)` share the `[1 x]` node and the trie level below it — so the read
  used to fetch the record behind every fact naming the term at argument 1 and keep the
  arity-1 ones.  A densely described individual therefore paid its whole description on
  every assert of a type for it, to find the handful of types it holds.  The unary
  roster (`reads/as-stored-unary-with-arg-global`) is the narrowing, and this is its
  gate.

  **The separation is what opens the arm**, and without it the check would measure
  nothing: `disjoint-problems` reads the argument's memberships only when a declaration
  reaches the checked type (`tax/separation-test` answers nil otherwise).  One
  declaration reaches `pbt_person` through its `genl` edge to `pbt_alpha`, about types
  the term does not hold, so it decides nothing here and this measures the cost of
  deciding that.

  `check` rather than `assert`: the decision is what is being measured, and `check`
  leaves the KB identical at every reading — no sentex, no settle — so the term's
  description is the only thing n moves."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(binary_predicate pbtLikes) 'CxPerf {:strength :monotonic})
    (v/assert kb '(disjoint pbt_alpha pbt_beta) 'CxPerf {:strength :monotonic})
    (v/assert kb '(genl pbt_person pbt_alpha) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pbtLikes 'PBTBusy (symbol (str "PBT" i)))
                  'CxPerf {:strength :monotonic})))
    (v/assert kb '(pbt_known PBTBusy) 'CxPerf {:strength :monotonic})
    (doall (for [_ (range 60)]
             (nanos (count (v/check kb '(pbt_person PBTBusy) 'CxPerf)))))))

(defn- mint-withdrawal-under-busy-term
  "A membership asserted about a term that n facts of an unrelated predicate already
  name, on a KB that prunes subsumed mints and holds one mint about another term.

  **The trigger `settle` runs on every membership it moves** with pruning on:
  `special/subsumed-mint-blocks` asks which mints the membership makes redundant.  The
  mints are read off the mint roster by term, so a term holding none costs a map lookup
  whatever else names it.  The mint about `PMWOther` keeps the roster non-empty, which is
  the gate in front of the lookup."
  [n]
  (binding [checks/*assertive-arg-types?*  true
            checks/*prune-subsumed-mints?* true]
    (let [kb (fresh-kb)]
      (v/assert kb '(genl pmw_animal thing) 'CxPerf {:strength :monotonic})
      (v/assert kb '(arg pmwOwns 1 pmw_animal) 'CxPerf {:strength :monotonic})
      (v/assert kb '(pmwOwns PMWOther PMWThing) 'CxPerf {:strength :monotonic})
      (v/with-deferred-settle kb
        (doseq [i (range n)]
          (v/assert kb (list 'pmwLikes 'PMWBusy (symbol (str "PMW" i)))
                    'CxPerf {:strength :monotonic})))
      (doall (for [i (range 60)]
               (nanos (v/assert kb (list (symbol (str "pmw_t" i)) 'PMWBusy) 'CxPerf {})))))))

(defn- settle-beside-withheld-mints
  "A fact of an unrelated predicate asserted into a KB that withholds n mints, each
  `(pwh_animal x)` drawn from `(pwhOwns x …)` while `(pwh_dog x)` says it more
  specifically.

  **The settle every write runs**, with pruning on: nothing records a withheld mint, so a
  settle that moves no membership, `genl` edge or `genlCx` edge reads nothing about the
  ones standing (`special/withheld-releases`)."
  [n]
  (binding [checks/*assertive-arg-types?*  true
            checks/*prune-subsumed-mints?* true]
    (let [kb (fresh-kb)
          m  {:strength :monotonic}]
      (v/assert kb '(genl pwh_animal thing) 'CxPerf m)
      (v/assert kb '(genl pwh_dog pwh_animal) 'CxPerf m)
      (v/assert kb '(arg pwhOwns 1 pwh_animal) 'CxPerf m)
      (v/with-deferred-settle kb
        (doseq [i (range n)
                :let [x (symbol (str "PWH" i))]]
          (v/assert kb (list 'pwh_dog x) 'CxPerf m)
          (v/assert kb (list 'pwhOwns x 'PWHThing) 'CxPerf m)))
      (doall (for [i (range 60)]
               (nanos (v/assert kb (list 'pwhLikes (symbol (str "PWHQ" i)) 'PWHThing)
                                'CxPerf {})))))))

(defn- mints-under-context-edge
  "One `(genlCx CxMceSub super)` edge over 50 contexts under `CxMceSub`, each holding one
  mint beside n authored memberships, with subsumed mints pruned.

  **The by-context read of the mint withdrawal** (`special/withdrawal-candidates`): the
  edge shows every context under `sub` what `super` holds, so the mints stated there are
  asked again.  They are read off the mint family's context leaves, so no membership
  stated beside them is read.  Each reading wires a fresh `super`, untimed but for the
  edge."
  [n]
  (binding [checks/*assertive-arg-types?*  true
            checks/*prune-subsumed-mints?* true]
    (let [kb (fresh-kb)
          m  {:strength :monotonic}]
      (v/assert kb '(genlCx CxMceSub CxUniverse) 'CxUniverse m)
      (v/assert kb '(genl mce_kind thing) 'CxUniverse m)
      (v/assert kb '(arg mceOwns 1 mce_kind) 'CxUniverse m)
      (doseq [i (range 50)
              :let [c (symbol (str "CxMce" i))]]
        (v/assert kb (list 'genlCx c 'CxMceSub) 'CxUniverse m)
        (v/assert kb (list 'mceOwns (symbol (str "MceA" i)) 'MceThing) c m)
        (v/bulk-assert-facts! kb (for [j (range n)]
                                   (list 'mce_known (symbol (str "MceK" i "x" j))))
                              c))
      (doall
       (for [i (range 60)
             :let [super (symbol (str "CxMceSuper" i))]]
         (do (v/assert kb (list 'genlCx super 'CxUniverse) 'CxUniverse m)
             (nanos (v/assert kb (list 'genlCx 'CxMceSub super) 'CxUniverse m))))))))

(defn- context-edge-beside-distant-mints
  "One `(genlCx CxCdmSub super)` edge whose `sub` holds one mint, beside n mints stated in
  16 contexts the edge does not reach, with subsumed mints pruned.

  **The other half of the by-context read**: the mint withdrawal reads the mints under
  `sub` one context leaf at a time (`special/withdrawal-candidates`), so the mints stated
  elsewhere are not read.  Each reading wires a fresh `super`, untimed but for the edge."
  [n]
  (binding [checks/*assertive-arg-types?*  true
            checks/*prune-subsumed-mints?* true]
    (let [kb (fresh-kb)
          m  {:strength :monotonic}]
      (v/assert kb '(genlCx CxCdmTop CxUniverse) 'CxUniverse m)
      (v/assert kb '(genlCx CxCdmSub CxCdmTop) 'CxUniverse m)
      (doseq [i (range 16)]
        (v/assert kb (list 'genlCx (symbol (str "CxCdmFar" i)) 'CxCdmTop) 'CxUniverse m))
      (v/assert kb '(genl cdm_kind thing) 'CxCdmTop m)
      (v/assert kb '(arg cdmOwns 1 cdm_kind) 'CxCdmTop m)
      (v/assert kb '(cdmOwns CdmHere CdmThing) 'CxCdmSub m)
      (v/with-deferred-settle kb
        (doseq [i (range n)]
          (v/assert kb (list 'cdmOwns (symbol (str "CdmA" i)) 'CdmThing)
                    (symbol (str "CxCdmFar" (mod i 16))) m)))
      (doall
       (for [i (range 60)
             :let [super (symbol (str "CxCdmSuper" i))]]
         (do (v/assert kb (list 'genlCx super 'CxUniverse) 'CxUniverse m)
             (nanos (v/assert kb (list 'genlCx 'CxCdmSub super) 'CxUniverse m))))))))

(defn- constraint-exposure-context-edge
  "A `genlCx` edge asserted into a KB holding n facts of a declared `functional`
  predicate in the context it newly sees.

  The edge is the one trigger the functional merge sweep
  (`special/equate-under-context-edge`) reaches *out* of the moved region for: visibility moved, so a pair already stored becomes jointly visible
  without either half being relabelled. Reaching out means walking the ancestor set, and an ancestor set
  is unbounded — a context cycle makes it the whole graph — so the walk is lazy and
  spends `*exposure-instance-budget*`.

  **The claim is flatness past the cap, and the cap is bound small here to reach it.**
  Below the cap the walk is proportional to the ancestor set and deliberately so: that is what
  the budget is *for*. The cap has to remain a cap — 8x the facts
  behind one edge costs the same once both sides are past it. With the budget above n, as
  the default 8192 is, the reading is the ancestor set and not the cap (5.42x at 250 →
  2000), which is the check answering a different question rather than a regression.

  Distinct subjects, so nothing in the ancestor set pairs: this measures the reach, not the
  deciding."
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

  `derive-functional-equalities` sweeps `(tax/context-down tax context)` only for a fact
  whose predicate a `functional` or `functionalInArg` mark reaches:
  `special/functional-mark-relevant?` is the per-fact gate that skips the closure read
  otherwise.  Without that gate, a mark anywhere in the KB makes every assert sweep, and an
  unrelated fact measured up to 75x slower at 6400 context readers.  This check fails when
  the gate is loosened.

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
  "100 facts arriving under a unary predicate carrying `(functionalInArg P 1)`, the empty
  determinant, where every stored tuple shares its determinant with every other, beside n
  such facts.  Each of the n facts and each of the 100 timed ones sits in its own context
  with no `genlCx` edge to anywhere, so no context sees two of them.

  The determinant is read once, when its second filler arrives, and a later tuple joins
  it with no read (`tuple/found-for`).  A member is a candidate only when a member with
  another filler sits in a context some context sees together with its own, which none
  here does, so no reader and no settle reads the n members.  No read on a fact's
  arrival spends `tax/*exposure-instance-budget*`, so the check runs at the default
  budget, above both sizes, and a read of the extent grows with n."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(functionalInArg p_empty_det 1) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (dotimes [i n]
        (v/assert kb (list 'p_empty_det i) (symbol (str "CxPed" i)) {})))
    (doall
     (for [i (range 100)]
       (nanos (v/assert kb (list 'p_empty_det (+ 1000000 i)) (symbol (str "CxPedT" i))
                        {}))))))

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

(defn- contrapositive-chain
  "`argue (pcf0 PCX)` over a `:monotonic` chain `pcf0 ⊑ … ⊑ pcfn` with a backward rule
  `(implies (pcg_i ?x) (not (pcf_i+1 ?x)))` per level and `(pcg_n-1 PCX)` stored.  The
  denial's search tries every level's rule, and each try asks whether the negated goal on
  `pcf0` fans to the rule's consequent (`res/contrapositive-predicates`).  The read holds
  `tax/contrapositive-closure`'s walk for the change clock's stretch, so the n tries walk
  the n-edge closure once; walking it per try is quadratic in n."
  [n]
  (let [kb (fresh-kb)
        x  (symbol "?x")]
    (dotimes [i n]
      (let [lo (symbol (str "pcf" i))
            hi (symbol (str "pcf" (inc i)))]
        (v/assert kb (list 'genl lo hi) 'CxPerf {:strength :monotonic})
        (v/assert-rule kb [(list (symbol (str "pcg" i)) x)] (list 'not (list hi x)) 'CxPerf
                       {:direction :backward})))
    (v/assert kb (list (symbol (str "pcg" (dec n))) 'PCX) 'CxPerf {:strength :monotonic})
    (doall (for [_ (range 60)]
             (nanos (v/argue kb '(pcf0 PCX) 'CxPerf {:max-depth 3}))))))

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

(def ^:private reconcile-edges
  "The `genl` edges `taxonomy-reconcile-moved` reads beside."
  50000)

(def ^:private reconcile-kb
  "The KB `taxonomy-reconcile-moved` reads: `reconcile-edges` edges in a four-way tree,
  built once on a space of its own, so the two sizes read the same taxonomy."
  (delay
    (let [kb (v/open-kb {:space [::taxonomy-reconcile] :recover? false})]
      (p/clear-records! (:records kb))
      (p/clear-index! (:index kb))
      (v/with-deferred-settle kb
        (doseq [i (range reconcile-edges)]
          (v/assert kb (list 'genl (symbol (str "prm" i "_t"))
                             (if (zero? i) 'thing (symbol (str "prm" (quot (dec i) 4) "_t"))))
                    'CxPerf {})))
      kb)))

(defn- taxonomy-reconcile-moved
  "A belief reconcile (`tax/refresh-beliefs`) naming n moved `genl` supporters beside
  `reconcile-edges` edges, read per thousand moved handles, with the supporter cache
  dropped before each so every read takes the index's supporter families.

  The reconcile reads the keys each moved handle installs and the supporters of each such
  key: a read per handle and per edge the region names, so the cost per moved handle is
  the same at any n.  A read that walks the relation or the store, once per settle, shows
  as the smaller region costing more per handle."
  [n]
  (let [kb     @reconcile-kb
        tax    (reasoning/taxonomy kb)
        tms    (reasoning/tms kb)
        hs     (vec (sort (reads/as-stored-with-functor (:index kb) 'genl)))
        moved  (into #{} (take n) (shuffle hs))
        in?    #(jtms/in? tms %)]
    (doall
     (for [_ (range 60)]
       (do (swap! tax assoc :supporters {:by-key {} :by-handle {}})
           ;; per thousand moved handles, which keeps a reading above `noise-floor-ns`
           (quot (* 1000 (nanos (tax/refresh-beliefs tax in? moved))) n))))))

(defn- flat-cache-belief-flip
  "One `(inverse P Q)` declaration defeated and revived over and over, in a KB carrying n
  `disjoint` declarations.  A `disjoint` is on the forced-monotonic roster, so no denial
  defeats one; `inverse` is not, and the same map holds both.

  The flat-cache twin of `taxonomy-belief-flip`, and the same claim on the other half of
  `tax/refresh-beliefs`: a belief move costs what *moved*, never what the KB declares.
  The supporter families hold the supporters of every flat cache, so their population
  is every disjoint pair, predicate property, `inverse` and declared arity in the KB
  together — a reconcile drawn over that is drawn over the vocabulary, and a corpus of
  OpenCyc's order carries tens of thousands.

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
    (v/assert kb '(inverse pfdLeftOf pfdRightOf) 'CxPerf {})
    (let [decl '(not (inverse pfdLeftOf pfdRightOf))]
      (doall
       (for [_ (range 120)]
         (nanos (let [h (v/assert kb decl 'CxPerf {:strength :monotonic})]
                  (v/retract! kb h))))))))

(defn- permuting-mark-defeat-flip
  "One `(symmetric P)` mark defeated below its facts and revived over and over, in a KB
  holding n facts on another symmetric predicate and 20 on P, each written against the
  sort.  Every flip moves which readers believe P's mark, so the 20 rows of P take a
  written spelling beside the fold and give it back (`chain/respell-rows!`).  The claim
  is that a defeat of a mark costs the rows of its predicate, never the facts under the
  other marks or the rest of the KB."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genlCx CxPermD CxPerf) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(symmetric pPermOther) 'CxPerf {})
    (v/assert kb '(symmetric pPermRel) 'CxPerf {})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pPermOther (symbol (str "PPZ" i)) (symbol (str "PPA" i))) 'CxPerf {}))
      (doseq [i (range 20)]
        (v/assert kb (list 'pPermRel (symbol (str "PRZ" i)) (symbol (str "PRA" i))) 'CxPerf {})))
    (let [denial '(not (symmetric pPermRel))]
      (doall
       (for [_ (range 60)]
         (nanos (let [h (v/assert kb denial 'CxPermD {:strength :monotonic})]
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

(defn- ground-goal-under-a-wide-fan
  "A ground binary goal `(pWfTop WfA WfB)` read uncached, under n sub-predicates of
  `pWfTop`, every other one across a `genlInverse` edge, ten of which store a fact on
  other terms.

  A matcher reads a goal once per member of its functor's fan, and the fan with a
  `genlInverse` edge in it was walked again per read, so the cost of a goal no member
  answers grew with the members.  A forward join tests one per row: a `different` test
  under 6,104 such members cost 76 ms.  The slot rosters cut the fan to the members storing
  the goal's arguments, and the walked fan is held for the clock stretch."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list (if (even? i) 'genl 'genlInverse) (symbol (str "pWf" i)) 'pWfTop)
                  'CxPerf {:strength :monotonic}))
      (doseq [i (range 10)]
        (v/assert kb (list (symbol (str "pWf" i)) 'WfC 'WfD) 'CxPerf {:strength :monotonic})))
    (let [goal '(pWfTop WfA WfB)]
      (doall (for [_ (range 40)]
               (nanos (dotimes [_ 100] (doall (res/matches-visible kb goal 'CxPerf false)))))))))

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
  O(clique·asserts) over the load.  `checks/disjoint-problems` builds the frame once
  through `tax/separation-test` for this reason.

  Distinct arriving terms, each pre-holding the same benign type, so nothing here is a
  clash and no term accumulates memberships: the reading is the cost of *deciding* a
  benign membership is admissible under a large clique, which is what every such assert
  on such a KB pays.

  Measured flat: 0.84-0.95x at 500 → 4000 clique members over three runs (the sub-1.0
  readings are the large size's JIT-warming bias `warm!` documents, not a speedup).  The
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
  would cost."
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

(defn- genl-closure-read
  "`genls` of a fresh type, asked right after the edge that places it under the bottom of
  an n-type braid: every type below the two that sit three and two above it, so the
  answer holds about n types and two paths reach most of them.

  The answer is n long, so the read is linear in n at best, and the claim is that it
  stays linear: an upward walk that reads each ancestor once.  `closure-membership` asks
  inside a closure already computed and `taxonomy-depth` times the edge's assert, so a
  read that re-derives each ancestor's own closure, quadratic on a braid, passes both."
  [n]
  (let [kb (fresh-kb)
        t  #(symbol (str "pgc" % "_t"))]
    (v/with-deferred-settle kb
      (doseq [i (range 3)]
        (v/assert kb (list 'genl (t i) 'thing) 'CxPerf {:strength :monotonic}))
      (doseq [i (range 3 n) p [(- i 3) (- i 2)]]
        (v/assert kb (list 'genl (t i) (t p)) 'CxPerf {:strength :monotonic})))
    (doall
     (for [k (range 20)
           :let [x (symbol (str "pgcx" k "_t"))]]
       (do (v/assert kb (list 'genl x (t (- n 1 (mod k 3)))) 'CxPerf {:strength :monotonic})
           (nanos (count (v/genls kb x))))))))

(defn- membership-check
  "A type membership arriving into a KB that already holds n of them, each about a
  *different* individual, each arrival giving its term a second type.  The term joins
  the index's kept terms (`kv/kept-adds`), and the write reads that term's own
  memberships and nothing about how many other terms are kept.  One term accumulating n
  types is `membership-beside-held-types`."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pm_a_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(genl pm_b_t thing) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)
           :let [x (symbol (str "PM" i))]]
       (do (v/assert kb (list 'pm_a_t x) 'CxPerf {:strength :monotonic})
           (nanos (v/assert kb (list 'pm_b_t x) 'CxPerf {:strength :monotonic})))))))

(defn- negation-arbitration
  "n **independent** P/¬P dilemmas — a fresh predicate and a fresh individual apiece, so
  no pair shares a body, a term or a context of concern with any other — and every assert
  settles beside them.

  The twin of `clash-arbitration`, for the other nogood source, and the same claim: an
  assert reads none of the standing pairs.  A settle re-deriving each standing pair from
  the store reads two belief-filtered `query` calls and a cross product per opposed body,
  which makes a load of N dilemmas Θ(N²).

  Nothing here is a *definitional* clash, so the pairs are the negation family's alone,
  placed as nogoods (`chain/place-negations!`)."
  [n]
  (let [kb (fresh-kb)]
    (doall
     (for [i (range n)
           :let [pr (symbol (str "pneg" i))
                 x  (symbol (str "PN" i))]]
       (do (v/assert kb (list pr x) 'CxPerf {})
           (nanos (v/assert kb (list 'not (list pr x)) 'CxPerf {})))))))

(defn- inherited-clash-arbitration
  "n standing inherited clashes, and an assert of an unrelated fact settling beside them.
  Each clash is a stored `:default` `(bigP lo2_i lo_i)` against the monotonic
  `(bigP hi_i hi2_i)`, which reaches its converse through `(genl lo_i hi_i)` and
  `(genl lo2_i hi2_i)` under `(asymmetric bigP)` and both positions preserved along `genl`.

  Every reason is monotonic, so each stored `:default` claim is the clash's loser.  One
  context (`split?` false): everything in `CxPerf`, each clash placed there.  Split: the
  stored claims in `CxPB`, the rest in `CxPA`, so each clash is placed at `CxPW` alone.  The clashes are built
  under one deferred settle, since they are the KB this measures against.  The timed fact
  reaches none of them: a `bigP` fact in one context, and a fact of `unrelP`, which no
  declaration preserves, in the split (`checks` says why)."
  [split? n]
  (let [kb      (fresh-kb)
        M       {:strength :monotonic}
        G       M
        [ca cb] (if split? '[CxPA CxPB] '[CxPerf CxPerf])
        t       (fn [s i] (symbol (str s i)))]
    (doseq [[k up] (if split?
                     '[[CxPA CxUniverse] [CxPB CxUniverse] [CxPW CxPA] [CxPW CxPB]]
                     '[[CxPerf CxUniverse]])]
      (v/assert kb (list 'genlCx k up) 'CxUniverse M))
    (doseq [d '[(binary_predicate bigP) (type_relation_predicate bigP) (asymmetric bigP)
                (transitiveInArgInverse bigP 1 genl) (transitiveInArgInverse bigP 2 genl)]]
      (v/assert kb d 'CxUniverse G))
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (t "plo_" i) (t "phi_" i)) ca G)
        (v/assert kb (list 'genl (t "plotwo_" i) (t "phitwo_" i)) ca G)
        (v/assert kb (list 'bigP (t "plotwo_" i) (t "plo_" i)) cb {})
        (v/assert kb (list 'bigP (t "phi_" i) (t "phitwo_" i)) ca M)))
    (doall
     (for [i (range 60)]
       (nanos (v/assert kb (list (if split? 'unrelP 'bigP) (t "pu_" i) (t "pv_" i)) cb {}))))))

(defn- inherited-entry-kb
  "A KB holding n stored claims that each keep an inherited-clash entry.  Each `(bigP
  pre_i plow)` in `CxPA` is denied by the `:default` reading of `(bigP phigh pre_i)` in
  `CxPB` through `(genl plow phigh)`, so its entry holds no nogood and a settle publishes
  nothing for it."
  [n]
  (let [kb (fresh-kb)
        t  (fn [s i] (symbol (str s i)))]
    (doseq [[k up] '[[CxPA CxUniverse] [CxPB CxUniverse]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse {:strength :monotonic}))
    (doseq [d '[(binary_predicate bigP) (type_relation_predicate bigP) (asymmetric bigP)
                (transitiveInArgInverse bigP 1 genl) (genl plow phigh)]]
      (v/assert kb d 'CxUniverse {}))
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'bigP (t "pre_" i) 'plow) 'CxPA {})
        (v/assert kb (list 'bigP 'phigh (t "pre_" i)) 'CxPB {})))
    kb))

(defn- inherited-entry-retraction
  "n carried inherited-clash entries (`inherited-entry-kb`), and a `retract!` of an
  unrelated fact settling beside them.  The retracted fact's handle is in the region with
  no record, and the discovery reads its sentence from the memo
  (`discovery/note-removed!`)."
  [n]
  (let [kb (inherited-entry-kb n)
        hs (mapv #(v/assert kb (list 'unrelP (symbol (str "pu_" %)) (symbol (str "pv_" %))) 'CxPA {})
                 (range 60))]
    (doall (for [h hs] (nanos (v/retract! kb h))))))

(defn- inherited-entry-declaration
  "n carried inherited-clash entries (`inherited-entry-kb`), and an assert of `(disjoint
  pdja_i pdjb_i)` between two types no claim names, settling beside them.  The
  declaration moves a flat-cache entry, which re-asks only the entries reading it
  (`discovery/flat-reading`)."
  [n]
  (let [kb (inherited-entry-kb n)]
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'disjoint (symbol (str "pdja_" i)) (symbol (str "pdjb_" i)))
                              'CxPA {}))))))

(defn- inherited-entry-except
  "n carried inherited-clash entries (`inherited-entry-kb`), and an assert of an `except`
  of an unrelated fact in `CxPC`, a context that sees no entry's members, settling beside
  them.  The except names a handle no entry's question read, so it re-asks no entry."
  [n]
  (let [kb (inherited-entry-kb n)
        _  (v/assert kb '(genlCx CxPC CxUniverse) 'CxUniverse {:strength :monotonic})
        hs (mapv #(v/assert kb (list 'unrelP (symbol (str "pu_" %)) (symbol (str "pv_" %))) 'CxPC {})
                 (range 60))]
    (doall (for [h hs] (nanos (v/assert kb (list 'except (list 'sentexHandle h)) 'CxPC {}))))))

(defn- recover-inherited-discovery
  "n stored `:default` claims `(bigP lo_i hi_i)` of a predicate preserved along `genl` at
  both positions, each argument under a chain of 60 shared types, so the product of a
  claim's two reaches (61 terms each) outnumbers the stored `bigP` extent at both sizes.
  Each reading is one `recover`, whose settle asks every claim with nothing carried,
  divided by n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        t  (fn [s i] (symbol (str s i)))]
    (v/assert kb '(genlCx CxPA CxUniverse) 'CxUniverse M)
    (doseq [d '[(binary_predicate bigP) (type_relation_predicate bigP) (asymmetric bigP)
                (transitiveInArgInverse bigP 1 genl) (transitiveInArgInverse bigP 2 genl)]]
      (v/assert kb d 'CxUniverse M))
    (v/with-deferred-settle kb
      (doseq [j (range 60)]
        (v/assert kb (list 'genl (t "pchain_" j) (t "pchain_" (inc j))) 'CxPA M))
      (doseq [i (range n)]
        (v/assert kb (list 'genl (t "plo_" i) 'pchain_0) 'CxPA M)
        (v/assert kb (list 'genl (t "phi_" i) 'pchain_0) 'CxPA M)
        (v/assert kb (list 'bigP (t "plo_" i) (t "phi_" i)) 'CxPA {})))
    (doall (for [_ (range 3)] (quot (nanos (v/recover kb)) n)))))

(defn- recover-discovery-own-out
  "n stored `:monotonic` claims `(carryP hold_kind Bone_i)` of a predicate preserved along
  `genl`, with one denial below, and n terms each a member of two types a `disjoint`
  separates, whose `except` withdraws it at its own context.  The discovery reads the live
  KB.  Each reading is one `recover`, divided by n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        U  'CxUniverse
        t  (fn [s i] (symbol (str s i)))]
    (v/with-deferred-settle kb
      (doseq [d '[(binary_predicate carryP) (transitiveInArgInverse carryP 1 genl)
                  (genl hold_kind animal) (genl cartx_kind hold_kind)
                  (genl sepa_kind animal) (genl sepb_kind animal)]]
        (v/assert kb d U M))
      (let [d (v/assert kb '(disjoint sepa_kind sepb_kind) U)]
        (v/assert kb (list 'except (list 'sentexHandle d)) U M))
      (doseq [i (range n)]
        (v/assert kb (list 'sepa_kind (t "Pair" i)) U M)
        (v/assert kb (list 'sepb_kind (t "Pair" i)) U M)
        (v/assert kb (list 'carryP 'hold_kind (t "Bone" i)) U M))
      (v/assert kb '(not (carryP cartx_kind Bone0)) U))
    (doall (for [_ (range 3)] (quot (nanos (v/recover kb)) n)))))

(defn- recover-discovery-separated-term
  "One term holding p types, each pair separated by a `disjoint` whose `except` withdraws
  it at its own context, so p(p-1)/2 nogoods over p members are placed.  One stored `:monotonic` claim of a predicate preserved
  along `genl`, with one denial below, makes the discovery ask.  Each reading is one
  `recover`, divided by the nogoods."
  [p]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        U  'CxUniverse
        t  (fn [s i] (symbol (str s i)))]
    (v/with-deferred-settle kb
      (doseq [d '[(binary_predicate carryP) (transitiveInArgInverse carryP 1 genl)
                  (genl hold_kind animal) (genl cartx_kind hold_kind)]]
        (v/assert kb d U M))
      (v/assert kb '(carryP hold_kind Bone0) U M)
      (v/assert kb '(not (carryP cartx_kind Bone0)) U)
      (doseq [i (range p)]
        (v/assert kb (list 'genl (t "sept_kind_" i) 'animal) U)
        (v/assert kb (list (t "sept_kind_" i) 'Many) U M))
      (doseq [i (range p) j (range (inc i) p)
              :let [d (list 'disjoint (t "sept_kind_" i) (t "sept_kind_" j))]]
        (v/assert kb (list 'except (list 'sentexHandle (v/assert kb d U))) U M)))
    (doall (for [_ (range 3)] (quot (nanos (v/recover kb)) (quot (* p (dec p)) 2))))))

(defn- recover-membership-sync
  "n terms each holding a member of an n-member `disjoint_metatype` and a type no
  separation reaches, so the first sync after a `recover` tests every kept term's pair
  (`membership/sync-memberships`).  Each type's separation frame is read once per sync, and
  a pair whose second type no separation reaches is not tested, so each term costs a
  constant.  Each reading is one `recover`, divided by n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (v/assert kb '(disjoint_metatype prms_meta) 'CxPerf M)
      (v/assert kb '(genl prms_plain thing) 'CxPerf M)
      (doseq [i (range n)]
        (v/assert kb (list 'prms_meta (symbol (str "prms_m" i))) 'CxPerf M))
      (doseq [i (range n)
              :let [x (symbol (str "PRMS" i))]]
        (v/assert kb (list 'prms_m0 x) 'CxPerf M)
        (v/assert kb (list 'prms_plain x) 'CxPerf M)))
    (doall (for [_ (range 3)] (quot (nanos (v/recover kb)) n)))))

(defn- negation-load
  "n negative facts whose bodies are stored in ONE polarity only — the negation-heavy load
  that carries no contradiction at all.

  The complement of `negation-arbitration`, and it guards the other half of the same
  namespace.  A settle that enumerated every stored negated body looking for a believed
  positive twin would be Θ(N²) here even though not one of these bodies has a twin; the
  opposed family (`kv/opposed-adds`) holds exactly the doubly-stored bodies, so this
  pays one count read.  The two checks fail for opposite reasons — this one if the
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
  otherwise leave its `natFormula` map and materialized types dangling a raw `nat/`
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

(def ^:private freezes-per-reading
  "Freezes of the fallback batched into one timed reading.  A vocabulary-sized fallback
  freezes in a few microseconds, below `noise-floor-ns`, so the reading is a fixed batch
  of them, the same batch at both sizes."
  40)

(defn- roots-fallback-section
  "n individuals written into a columnar store as a reindex writes them — two memberships
  and a relation each, and one taxonomy supporter of each individual's own type — and then
  the roots' fallback frozen as the snapshot writes it, a fixed batch per reading, and
  thawed whole at the next open.

  The vocabulary is three predicates and one context at both sizes.  What grows is the
  terms, their argument slots and memberships, and the taxonomy keys with their supporters
  — the families a large KB's fallback holds — so a fallback that
  holds any of them grows with n, and one holding the vocabulary's counters alone is flat."
  [n]
  (let [st (columnar/columnar-index-store {:space [::fallback]})]
    (p/clear-index! st)
    (dotimes [i n]
      (let [x (symbol (str "PR" i)) t (symbol (str "prt" i)) h (* 4 i)]
        (p/index-sentex st (sx/sentex (list 'prbird x) 'CxPerf {}) h)
        (p/index-sentex st (sx/sentex (list 'prpet x) 'CxPerf {}) (+ h 1))
        (p/index-sentex st (sx/sentex (list 'prlikes x (symbol (str "PR" (inc i)))) 'CxPerf {}) (+ h 2))
        (p/family-apply! st [[:post :tax-support [:genl t 'prbird 'CxPerf] (+ h 3)]
                             [:post :tax-installs [(+ h 3)] [:genl t 'prbird]]])))
    (let [fe (vec (dense-roots/fallback-entries (:roots st)))]
      (doall (for [_ (range 10)]
               (nanos (dotimes [_ freezes-per-reading] (nippy/freeze fe))))))))

(defn- exception-roster-gate
  "`reads/watched-rule?` against a roster of n rules — the gate `chain/rule-view-of` takes
  once per candidate rule per new datum, before it will fetch a rule's exceptions.

  The gate is specified as an O(1) membership test, and the firing path is
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
    (doseq [i (range n)] (rules/index-exception st i ['pexc]))
    (doall
     (for [r (range 200)]
       (nanos (dotimes [i reads-per-reading]
                (reads/watched-rule? st (mod (+ i r) n))))))))

(defn- trigger-keys-beside-rules
  "`rules/trigger-keys` for a positive and a negated fact on a predicate no rule reads,
  against n rules each reading a predicate of its own, on the `:dense` index.

  `chain/fire-rules-for` asks it once per datum a chaining run touches.  A read of the
  rule index's root level builds a set of every stored key on the `:dense` index, so a
  read of it per datum grows with n, and a membership test per closure term does not."
  [n]
  (let [st  (dense/dense-index-store {:space [::trigger]})
        tax (reasoning/taxonomy (fresh-kb))]
    (p/clear-index! st)
    (doseq [i (range n)] (rules/index-rule st i [(symbol (str "pTkR" i))] nil 'CxPerf))
    (doall
     (for [_ (range 100)]
       (nanos (dotimes [_ reads-per-reading]
                (rules/trigger-keys tax '(pTkFact TkA) st)
                (rules/trigger-keys tax '(not (pTkFact TkA)) st)))))))

(defn- overlay-selectivity
  "`reads/stored-count-in-context` on a fork, for a context root of n handles the fork has
  never touched — a flat posting's cardinality, read through the overlay's `kv-count`.
  The planner's other cardinality reads (`reads/stored-count-with-functor`,
  `reads/stored-count-with-arg-in`) read a count trie's counter, which an untouched fork
  reads straight through.

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
    (doseq [i (range n)] (p/kv-add-to-set base [:context-root 'CxPovl] i))
    (let [own (mem/memory-kv-backend {:space [::ovfork]})
          _   (p/kv-clear! own)
          st  (kv/->KvIndexStore (okv/overlay-kv own (frozen/frozen-kv base)))]
      (doall
       (for [_ (range 200)]
         (nanos (dotimes [_ reads-per-reading] (reads/stored-count-in-context st 'CxPovl))))))))

(defn- intersect-selectivity
  "`sentexes-with-args` for a pattern pinning a **rare** argument beside a **hot** one
  on the same predicate — `(pint ?x PIA PIB)` with four handles at position 1 against n
  at position 2, all stated in one context — which is one `kv-intersect` over the two
  argument-root leaves, `[pint 1 PIA CxPI]` ∩ `[pint 2 PIB CxPI]`.  A single bound
  argument intersects nothing (the node's leaf is handed back), so two bound positions
  are the structure that exercises `kv-intersect`.

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
    (doseq [i (range n)] (p/kv-add-to-set b [:argument-root :handles '[pint 2 PIB CxPI]] i))
    (doseq [i (range 4)] (p/kv-add-to-set b [:argument-root :handles '[pint 1 PIA CxPI]] (* 7 i)))
    (doseq [node '[[pint 1 PIA] [pint 2 PIB]]]
      (p/kv-add-to-set b [:argument-root :children node] 'CxPI))
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
  per literal per plan.  `reads/stored-count-children` answers it off a set's cardinality
  or an edge span; `(count (children …))` would answer the same number by materializing the child
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

(defn- solve-rule-grounding
  "Grounding a recursive `set/solveRule` over a chain of `n` hops from a chosen root —
  reachability, the case a solve rule's recursion is for.  Even hops are choice edges and
  odd ones background links, so the chain continues only through both of the grounding's
  joins: a program literal matched against the atoms the round before derived, and the
  background bindings read by the variable that atom binds.

  A chain of `n` atoms is `n` semi-naive rounds of one new atom each.  A round that
  rebuilt its atom indexes, or walked every background binding rather than those its new
  atom reaches, would cost O(n), and the grounding O(n²) — 16x per atom between these
  sizes, where the indexes a round carries over read flat.  Each reading is one whole
  grounding, per thousand atoms, so it sits well above the noise floor."
  [n]
  (let [kb    (fresh-kb)
        build (var-get #'sc/build)
        nd    #(symbol (str "PsrN" %))]
    (v/assert-many kb
                   (cons (list 'perf_sr_root_cand (nd 0))
                         (for [i (range n)]
                           (list (if (even? i) 'perfSrCand 'perfSrLink) (nd i) (nd (inc i)))))
                   'CxPerf {:chain? false})
    (doseq [r '[(set/assumptionRule (implies (perf_sr_root_cand ?x) (perf_sr_root ?x)))
                (set/assumptionRule (implies (perfSrCand ?x ?y) (perfSrEdge ?x ?y)))
                (set/inertRule (set/solveRule (implies (perf_sr_root ?x) (perf_sr_reach ?x))))
                (set/inertRule (set/solveRule (implies (and (perf_sr_reach ?x) (perfSrEdge ?x ?y))
                                                       (perf_sr_reach ?y))))
                (set/inertRule (set/solveRule (implies (and (perf_sr_reach ?x) (perfSrLink ?x ?y))
                                                       (perf_sr_reach ?y))))]]
      (v/assert kb r 'CxPerf))
    (doall
     (for [_ (range 8)]
       (/ (* 1000.0 (nanos (build kb 'CxPerf))) n)))))

(defn- label-beside-unrelated-facts
  "Two choice rules and one candidate in `CxPerf` beside `n` facts no rule reads, and sixty
  groundings of the program (`solve-context/build`).  A run finds its rules off the
  `:solve-rules` roster, so a grounding reads two rules and one candidate at any `n`; a
  walk of the base's extent for the rules reads every fact there, once per rule kind."
  [n]
  (let [kb    (fresh-kb)
        build (var-get #'sc/build)]
    (v/assert-many kb
                   (cons '(perf_lb_cand PlbItem)
                         (for [i (range n)] (list 'perf_lb_noise (symbol (str "PlbX" i)))))
                   'CxPerf {:chain? false})
    (v/assert kb '(set/assumptionRule (implies (perf_lb_cand ?c) (perfLbColor ?c red))) 'CxPerf)
    (v/assert kb '(set/assumptionRule (implies (perf_lb_cand ?c) (perfLbColor ?c blue))) 'CxPerf)
    (doall (for [_ (range 60)] (nanos (build kb 'CxPerf))))))

(defn- arity-reach-trigger
  "n **conforming** facts of a predicate whose arity was declared before any of them.

  A binding refreshes the shapes of the functors below it when it arrives, and a fact of a
  declared predicate is no binding: the store hook asks whether its shape breaks its
  functor's length (`arity/inert-tuple?`), answered from the length entries, and queues
  nothing for a conforming one.  So an ordinary fact arriving must cost the same at 2,000 as at 250, and
  a recompute run per fact turns a linear load quadratic here and in no test.

  Conforming on purpose: a violating fact is held inert, which is
  `arity-binding-arrival`'s workload; what this separates is a pass
  that runs per fact from one that runs per binding."
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
  expensive case rather than a degenerate one: `arity/relation-length` answers off a
  binding read for a predicate carrying a length of its own and off a walk of its
  super-predicates for one that does not, so a KB that has stated no arity is the KB
  where every declaration pays the walk.  The cost is `O(declarations × super-predicates)`
  and this check pins the first factor.

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
  declaration's arity read is `arity/relation-length`, which walks the supers of a
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

(defn- store-past-checks!
  "Write `sentences` into CxUniverse of `kb`'s store the way a foreign store holds them:
  through a second KB over the same space whose taxonomy was never built, so no
  assert-time check reads what `kb` holds, then `recover` `kb` over the result.  A
  cycle-closing `genlCx` edge is refused at assert and `genlCx` is on the
  forced-monotonic roster, so no belief race forms one either: a context cycle reaches
  the taxonomy only from such a store (docs/taxonomy.md).  Answers the handles."
  [kb sentences]
  (let [raw (v/open-kb {:space 9 :recover? false})
        hs  (binding [v/*write-unrecovered?* true]
              (mapv #(v/assert raw % 'CxUniverse {}) sentences))]
    (v/recover kb)
    hs))

(defn- retract-context-cycle-scaling
  "One `retract!` of a `genlCx` edge **inside a two-context cycle**, on a KB whose
  context graph holds n unrelated contexts beside it.

  Two contexts that see each other sit in a strongly connected component, and a deletion
  inside one can split it.  A split is the only edit that invalidates the component map,
  and the map is what `sees?` reads for its O(1) same-component answer, so it may not be
  left stale.  What the repair may cost is that component; what it may not cost is the
  graph around it, which is the claim measured here.

  Each cycle is `PcB → PcA` asserted and `PcA → PcB` written past the checks
  (`store-past-checks!`), so the two contexts see each other once `kb` recovers.

  One cycle per victim, because a handle can only be retracted once and a broken cycle
  cannot be broken again.  `populate!` asserts the n unrelated contexts: by default each
  under one top context, in no cycle; `context-ring!` puts them all in one cycle, so the
  component map holds n entries the victims are not among.  No retraction names them, and
  the count is the same at the last reading as at the first."
  ([n] (retract-context-cycle-scaling
        (fn [kb n]
          (v/with-deferred-settle kb
            (doseq [i (range n)]
              (v/assert kb (list 'genlCx (pctx "PcBg" i) 'CxPcTop) 'CxUniverse {}))))
        n))
  ([populate! n]
   (let [kb (fresh-kb)]
     (populate! kb n)
     (v/with-deferred-settle kb
       (doseq [i (range retract-victims)]
         (v/assert kb (list 'genlCx (pctx "PcA" i) 'CxPcTop) 'CxUniverse {})
         (v/assert kb (list 'genlCx (pctx "PcB" i) (pctx "PcA" i)) 'CxUniverse {})))
     ;; the closing PcA → PcB edges are the timed victims; the recover builds the
     ;; component map and ranks the relation before a single reading is taken
     (let [victims (store-past-checks! kb (mapv #(list 'genlCx (pctx "PcA" %) (pctx "PcB" %))
                                                (range retract-victims)))]
       (doall (for [h victims] (nanos (v/retract! kb h))))))))

(defn- genlcx-chain-moved-beside-a-nogood
  "A chain of n `genlCx` edges asserted in one settle pass beside a membership nogood, per
  edge, each reading on a KB of its own.

  ```
  CxPerf    (disjoint gcn_a gcn_b)   (gcn_a PGcn)   (gcn_b PGcn)
   └─ CxGcnN<n-1> ← … ← CxGcnN1 ← CxGcnN0
  ```

  The membership family holds the nogood, so `chain/place-nogoods!` forces the pass's
  `:reach` (`special/drain-context-moves!`).  Its `:below` reads, per lower end, every
  context the contexts under it see (`tax/context-move`'s `:seen`), which one walk up from
  those contexts answers.  A union of their ancestor sets costs the chain under the end
  times the chain above it, a cube of the chain over the pass."
  [n]
  (doall (for [_ (range 4)]
           (let [kb (fresh-kb)
                 M  {:strength :monotonic}
                 c  #(pctx "GcnN" %)]
             (v/assert kb '(disjoint gcn_a gcn_b) 'CxPerf M)
             (v/assert kb '(gcn_a PGcn) 'CxPerf {})
             (v/assert kb '(gcn_b PGcn) 'CxPerf {})
             (quot (nanos (v/with-deferred-settle kb
                            (v/assert kb (list 'genlCx (c (dec n)) 'CxPerf) 'CxUniverse M)
                            (doseq [i (range (dec n))]
                              (v/assert kb (list 'genlCx (c i) (c (inc i))) 'CxUniverse M))))
                   n)))))

(defn- recover-over-a-context-chain
  "One `recover` of a KB holding a chain of n `genlCx` edges and nothing else, per edge,
  eight readings.  No family holds a nogood, so no placement reads the pass's `genlCx`
  moves, and `chain/place-nogoods!` leaves unforced the `:reach` whose `:below` walks
  each lower end's ancestor set (`special/drain-context-moves!`)."
  [n]
  (let [kb (fresh-kb)
        c  #(pctx "RcN" %)]
    (v/with-deferred-settle kb
      (doseq [i (range (dec n))]
        (v/assert kb (list 'genlCx (c i) (c (inc i))) 'CxUniverse {})))
    (doall (for [_ (range 8)] (quot (nanos (v/recover kb)) n)))))

(defn- context-ring!
  "Put n contexts `CxPr0 … CxPr(n-1)` into one `genlCx` cycle, `CxPr(i) → CxPr(i+1)` and
  `CxPr(n-1) → CxPr0`: the chain asserted, the closing edge written past the checks
  (`store-past-checks!`).  The relation then holds one component of n members."
  [kb n]
  (let [edge #(list 'genlCx (pctx "Pr" %1) (pctx "Pr" %2))]
    (v/with-deferred-settle kb
      (doseq [i (range (dec n))]
        (v/assert kb (edge i (inc i)) 'CxUniverse {})))
    (store-past-checks! kb [(edge (dec n) 0)])))

(defn- assert-context-edge-beside-cycle
  "One `assert` of a `genlCx` edge between two fresh contexts, on a KB whose context graph
  holds a cycle of n contexts the edge does not touch.

  Both endpoints are fresh, so both sit at depth 0 and the insert lifts the source above
  the target.  A lift moves the source's whole component, and the source is in none, so
  the repair's cost is one node and the n-member component beside it is not read."
  [n]
  (let [kb (fresh-kb)]
    (context-ring! kb n)
    (doall (for [i (range retract-victims)]
             (nanos (v/assert kb (list 'genlCx (pctx "PeA" i) (pctx "PeB" i))
                              'CxUniverse {}))))))

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

(defn- closure-rule-under-departing-context-edge
  "One `retract!` of a `(genlCx CxCrdSub CxCrdTop)` edge whose upper context holds n
  `genl` facts below `crd_top`, n-1 of them `crd_marked`, and one forward rule joining
  the two, so a full join of the rule reads n tuples.  The rule concludes `(crd_hit
  crd_t0)` in `CxCrdSub` through the edge, so the retraction sweeps the conclusion and
  re-chains what `CxCrdTop` holds (`special/resubsumption-seeds`): the n `genl` facts,
  the marks and the rule.  Each `genl` seed is a closure edge datum, and one chaining
  run re-joins the rule in full once per closure stamp (`chain/*closure-rejoins*`):
  one n-tuple join per retraction rather than n of them.  Each reading restores the
  edge, untimed."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genlCx CxCrdTop CxUniverse) 'CxUniverse m)
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [t (symbol (str "crd_t" i))]]
        (v/assert kb (list 'genl t 'crd_top) 'CxCrdTop m)
        (when (pos? i) (v/assert kb (list 'crd_marked t) 'CxCrdTop m))))
    (v/assert kb '(set/forwardRule (implies (and (genl ?t crd_top) (crd_marked ?t)) (crd_hit ?t)))
              'CxCrdTop m)
    (v/assert kb '(crd_marked crd_t0) 'CxCrdSub m)
    (doall (for [_ (range retract-victims)]
             (let [h (v/assert kb '(genlCx CxCrdSub CxCrdTop) 'CxUniverse m)]
               (nanos (v/retract! kb h)))))))

(defn- separation-rule-under-moving-edge
  "One `genl` edge placing a fresh type under a part of a `partition`, asserted and then
  retracted, on a KB holding CxUniverse's emptiness rule shape, `(disjoint ?type ?type)` with
  `(unary ?type)`, and n `unary` types under no separation.  The edge moves the separation
  of the fresh type alone, so the re-join it owes reads that type
  (`special/recheck-on-separation`); a re-join over every `unary` type costs n per edge."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(partition psm_whole psm_a psm_b) 'CxPerf m)
    (v/assert kb '(set/forwardRule (implies (and (disjoint ?type ?type) (unary ?type))
                                            (empty ?type)))
              'CxPerf m)
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [t (symbol (str "psm_o" i "_t"))]]
        (v/assert kb (list 'genl t 'thing) 'CxPerf m)
        (v/assert kb (list 'unary t) 'CxPerf m)))
    (doall (for [i (range retract-victims)
                 :let [t (symbol (str "psm_x" i "_t"))]]
             (do (v/assert kb (list 'unary t) 'CxPerf m)
                 (nanos (v/retract! kb (v/assert kb (list 'genl t 'psm_a) 'CxPerf m))))))))

(defn- context-edge-retraction-beside-its-own-mint
  "One `retract!` of a `(genlCx CxOmSub CxOmTop)` edge whose upper context holds n
  `omLink` facts, each typed by `(arg omLink 1 om_node)` and read by a forward rule, on a
  KB declaring `(arg genlCx 1 context)`.  The edge mints `(context CxOmSub)`, and the
  teardown removes the edge and that mint.  The mint types the edge itself rather than
  resting on a route through it (`special/edge-own-mints`), so the retraction owes no
  re-chain of the n facts, each of which would re-run its entailments and the rule.
  Each reading restores the edge, untimed."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (doseq [s '[(genl context thing) (genl om_node thing)
                (arg genlCx 1 context) (arg omLink 1 om_node)]]
      (v/assert kb s 'CxUniverse m))
    (v/assert kb '(genlCx CxOmTop CxUniverse) 'CxUniverse m)
    (v/assert kb '(set/forwardRule (implies (omLink ?x ?y) (om_linked ?x))) 'CxOmTop m)
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'omLink (symbol (str "OmItem" i)) 'OmHub) 'CxOmTop m)))
    (doall (for [_ (range retract-victims)]
             (let [h (v/assert kb '(genlCx CxOmSub CxOmTop) 'CxUniverse m)]
               (nanos (v/retract! kb h)))))))

(defn- context-edge-retraction-beside-sighted-facts
  "One `retract!` of a `(genlCx sub CxDsTop)` edge, where a forward rule in `CxDsTop`
  reads `dsLink`, `CxDsTop` holds n `dsLink` facts, and `sub` holds one, so the rule
  concludes `(ds_linked …)` in `sub` through the edge.  The teardown removes the edge and
  that conclusion, and re-chains the antecedents of the firing that named the edge
  (`special/sighting-seeds`): one fact at both n, and not the n facts `CxDsTop` shows.
  Each reading wires a fresh `sub` and asserts the edge and its fact, untimed."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genlCx CxDsTop CxUniverse) 'CxUniverse m)
    (v/assert kb '(set/forwardRule (implies (dsLink ?x ?y) (ds_linked ?x))) 'CxDsTop m)
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'dsLink (symbol (str "DsItem" i)) 'DsHub) 'CxDsTop m)))
    (doall (for [i (range retract-victims)
                 :let [sub (symbol (str "CxDsSub" i))
                       h   (v/assert kb (list 'genlCx sub 'CxDsTop) 'CxUniverse m)]]
             (do (v/assert kb (list 'dsLink (symbol (str "DsMine" i)) 'DsHub) sub m)
                 (nanos (v/retract! kb h)))))))

(defn- filler-beside-clashing-fillers
  "One `:default` filler of `(pFcf FcfSubj _)` asserted and retracted beside n stored
  fillers, under `(functional pFcf)`, so the determinant holds n(n-1)/2 nogoods.  The
  filler's arrival queues itself and not its partners (`tuple/classify-det-member`), and
  its n placements leaving with it queue nothing (`tuple/note-placement-left!`), so
  each write places or removes the filler's n nogoods and no others."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(functional pFcf) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pFcf 'FcfSubj (symbol (str "FcfVal" i))) 'CxPerf {})))
    (doall (for [i (range retract-victims)]
             (nanos (v/retract! kb (v/assert kb (list 'pFcf 'FcfSubj (symbol (str "FcfNew" i)))
                                             'CxPerf {})))))))

(defn- except-merge-scaling
  "One `except` of an equality asserted and retracted, on a KB carrying n standing
  `sameAs` merges that each displace one fact.

  An `except` moves which equalities a datum's own context sees without any relabel
  saying so, and the settle's supersession reconcile has to re-examine the data it can
  change (docs/equational.md, \"An except of an equation\").  Re-examining every standing
  displaced spelling instead makes each except of a merge linear in the merges the KB
  holds.  Each victim is its own merge over its own displaced fact, disjoint from the n
  standing ones, so the reconcile the except owes is one entry at both sizes."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pMergeBorn (symbol (str "PMHi" i)) 'PMPlace) 'CxPerf {})
        (v/assert kb (list 'sameAs (symbol (str "PMAa" i)) (symbol (str "PMHi" i)))
                  'CxPerf {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pMergeBorn (symbol (str "PXHi" i)) 'PMPlace)
                                    'CxPerf {})
                          (v/assert kb (list 'sameAs (symbol (str "PXAa" i)) (symbol (str "PXHi" i)))
                                    'CxPerf {}))
                        (range retract-victims))]
      (doall (for [h victims]
               (nanos (v/retract! kb (v/assert kb (list 'except (list 'sentexHandle h)) 'CxPerf
                                               {:strength :monotonic}))))))))

(defn- irreflexive-mark-arrival
  "One `irreflexive` mark asserted, read through and retracted, over a predicate holding n
  ordinary tuples beside one `:default` self tuple.

  The mark takes the self tuple out of belief and leaves its label IN: the settle places
  the nogood's `contradicts` and `defeat` from the candidate index (docs/nmtms.md, \"A
  nogood placed as a conclusion\"), so neither the arrival, its settle nor the first read
  at the tuple's context reads an ordinary tuple."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pIrrMark (symbol (str "PIM" i)) 'PIMHub) 'CxPerf {})))
    (let [self (v/assert kb '(pIrrMark PIMSelf PIMSelf) 'CxPerf {})]
      (doall (for [_ (range retract-victims)]
               (nanos (let [m (v/assert kb '(irreflexive pIrrMark) 'CxPerf {:strength :monotonic})]
                        (v/believed? kb self 'CxPerf)
                        (v/retract! kb m))))))))

(defn- verdict-window-write
  "A self tuple arriving in a context of its own under an `irreflexive` mark, beside n
  consequences of one other convicted self tuple, each stored in a context of its own.

  ```
  CxPerf  (irreflexive pvwNear) (irreflexive pvwFar)
   ├─ CxPVN  (pvwNear PVWA PVWA)
   │   └─ CxPVR0 … each  (pvwNear ?x ?x) => (pvwTag ?x PVWVi)
   └─ CxPVW0 … each timed  (pvwFar PVWFj PVWFj)
  ```

  The near tuple's placed defeat hides each of the n consequences at its own context.  A
  listener is registered, so each timed write takes a report (docs/nmtms.md, \"The
  published window\"); a report that read every standing defeat's consequences at their
  own contexts pays for the n consequences here."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(irreflexive pvwNear) 'CxPerf m)
    (v/assert kb '(irreflexive pvwFar) 'CxPerf m)
    (v/assert kb '(genlCx CxPVN CxPerf) 'CxUniverse m)
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [c (symbol (str "CxPVR" i))]]
        (v/assert kb (list 'genlCx c 'CxPVN) 'CxUniverse m)
        (v/assert kb (list 'set/forwardRule
                           (list 'implies '(pvwNear ?x ?x) (list 'pvwTag '?x (symbol (str "PVWV" i)))))
                  c m))
      (doseq [j (range 60)]
        (v/assert kb (list 'genlCx (symbol (str "CxPVW" j)) 'CxPerf) 'CxUniverse m))
      (v/assert kb '(pvwNear PVWA PVWA) 'CxPVN {}))
    (v/watch kb (fn [_] nil))
    (doall
     (for [j (range 60)
           :let [x (symbol (str "PVWF" j))]]
       (nanos (v/assert kb (list 'pvwFar x x) (symbol (str "CxPVW" j)) {}))))))

(defn- reader-scoped-write
  "A write beside n readers, each holding a placed `:default` self tuple under an
  `irreflexive` mark, eight of them an inherited clash too: a fact in a context no reader sees,
  alternating with a self tuple at one reader.

  ```
  CxUniverse  (irreflexive pRsSelf) (transitiveInArgInverse pRsCarries 1 genl)
              (genl prs_cart prs_hauler) (pRsCarries prs_hauler PRsBone_i), i < 8
   ├─ CxPerfRsSide        timed  (pRsLedger PRsL_j PRsX)
   └─ CxPerfRsTop
       └─ CxPRsR0 …  (pRsSelf PRsA_i PRsA_i), (not (pRsCarries prs_cart PRsBone_i)) for i < 8
                     timed  (pRsSelf PRsB_j PRsB_j)
  ```

  A move reaches the nogoods whose candidates it moves (docs/nmtms.md, \"The nogood
  families\"), so a write places again at most the one nogood at one reader, and the
  discovery's entries are carried.  A write placing every reader's nogood again reads
  here as growth."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        rs (mapv #(symbol (str "CxPRsR" %)) (range n))]
    (v/with-deferred-settle kb
      (doseq [c '[CxPerfRsTop CxPerfRsSide]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse M))
      (doseq [s '[(irreflexive pRsSelf) (binary_predicate pRsCarries)
                  (transitiveInArgInverse pRsCarries 1 genl) (genl prs_hauler animal)
                  (genl prs_cart prs_hauler)]]
        (v/assert kb s 'CxUniverse M))
      (doseq [[i r] (map-indexed vector rs)
              :let [x (symbol (str "PRsA" i)) bone (symbol (str "PRsBone" i))]]
        (v/assert kb (list 'genlCx r 'CxPerfRsTop) 'CxUniverse M)
        (v/assert kb (list 'pRsSelf x x) r {})
        (when (< i 8)
          (v/assert kb (list 'pRsCarries 'prs_hauler bone) 'CxUniverse M)
          (v/assert kb (list 'not (list 'pRsCarries 'prs_cart bone)) r {}))))
    (doall (for [j (range 60)
                 :let [x (symbol (str (if (even? j) "PRsL" "PRsB") j))]]
             (nanos (if (even? j)
                      (v/assert kb (list 'pRsLedger x 'PRsX) 'CxPerfRsSide {})
                      (v/assert kb (list 'pRsSelf x x) (nth rs (mod j n)) {})))))))

(defn- standing-nogood-write
  "A membership joining a dilemma at `CxPerfSnR`, beside n standing `disjoint` dilemmas
  placed there, each two `:default` memberships of one term.  With `first` the options of
  each term's first membership, `{:strength :monotonic}` makes every nogood a
  `:monotonic` membership and its loser, and the timed membership joins one as its loser.

  ```
  CxUniverse  (disjoint psn_dog psn_cat)
   └─ CxPerfSnR   (psn_dog PSnA_i) first and (psn_cat PSnA_i), i < n
                  timed  (psn_cat PSnB_j) beside (psn_dog PSnB_j) first
  ```

  The placement pass places the nogoods whose candidates the write moves, which with a
  loser is the nogood of the loser that arrived, and keeps every other placement
  (docs/nmtms.md, \"The nogood families\").  A pass placing every standing nogood again
  reads here as growth."
  ([n] (standing-nogood-write n {}))
  ([n first]
   (let [kb (fresh-kb)
         M  {:strength :monotonic}]
     (v/with-deferred-settle kb
       (v/assert kb '(genlCx CxPerfSnR CxUniverse) 'CxUniverse M)
       (doseq [s '[(genl psn_dog animal) (genl psn_cat animal) (disjoint psn_dog psn_cat)]]
         (v/assert kb s 'CxUniverse M))
       (doseq [i (range n) :let [a (symbol (str "PSnA" i))]]
         (v/assert kb (list 'psn_dog a) 'CxPerfSnR first)
         (v/assert kb (list 'psn_cat a) 'CxPerfSnR {}))
       (doseq [j (range 60)] (v/assert kb (list 'psn_dog (symbol (str "PSnB" j))) 'CxPerfSnR first)))
     (doall (for [j (range 60)]
              (nanos (v/assert kb (list 'psn_cat (symbol (str "PSnB" j))) 'CxPerfSnR {})))))))

(defn- candidate-write
  "A self tuple arriving under an `irreflexive` mark in a context of its own, beside n
  standing self tuples the mark convicts in a sibling context.

  ```
  CxUniverse  (irreflexive pCwSelf)
   ├─ CxPerfCwBig  (pCwSelf PCwA_i PCwA_i), i < n
   └─ CxPerfCwW    timed  (pCwSelf PCwB_j PCwB_j)
  ```

  Each timed tuple is a candidate the write adds.  The candidates by context are read
  again for the handles the write journals (`decide/synced`), and the new tuple's reader
  reads the self tuples stored in its ancestor set (docs/nmtms.md, \"The candidate
  journal\"), so the write reads none of the n.  A write recomputing the
  closure of every candidate, or fetching every candidate's record, reads here as growth."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (doseq [c '[CxPerfCwBig CxPerfCwW]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse M))
      (v/assert kb '(irreflexive pCwSelf) 'CxUniverse M)
      (doseq [i (range n)
              :let [x (symbol (str "PCwA" i))]]
        (v/assert kb (list 'pCwSelf x x) 'CxPerfCwBig {})))
    (doall (for [j (range 60)
                 :let [x (symbol (str "PCwB" j))]]
             (nanos (v/assert kb (list 'pCwSelf x x) 'CxPerfCwW {}))))))

(defn- reached-reader-family-read
  "A functional pair completed at `CxPerfRfR`, beside n/4 candidates each of four families
  stated in sixteen sibling contexts the reader does not see.

  ```
  CxUniverse  (anti_symmetric pRfAnti) (functional pRfFun) (anti_transitive pRfCh)
              (arity pRfLen 2)
   ├─ CxPerfRf<k>, k < 16  for i ≡ k mod 16, i < n/4: (pRfAnti PRfA_i PRfB_i) and its
   │                       converse, (pRfFun PRfA_i PRfB_i) and (pRfFun PRfA_i PRfC_i),
   │                       the chain (pRfCh PRfA_i PRfB_i) (pRfCh PRfB_i PRfC_i)
   │                       (pRfCh PRfA_i PRfC_i), and (pRfLen PRfA_i PRfB_i PRfC_i) :monotonic
   └─ CxPerfRfR            timed  (pRfFun PRfR_j PRfC) beside (pRfFun PRfR_j PRfB)
  ```

  Each write makes a determinant pair at the reader, which the settle places; each family
  reads its candidates stated in the reader's ancestor set (`decide/handles-at`,
  docs/nmtms.md, \"The candidate journal\").  The ternary tuples are held `:monotonic`,
  so they clash hard and no loser is hidden at its own context.  A family reading its
  whole candidate set at the reader reads here as growth."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        cx #(symbol (str "CxPerfRf" (mod % 16)))
        s  #(symbol (str %1 %2))]
    (v/with-deferred-settle kb
      (doseq [i (range 16)] (v/assert kb (list 'genlCx (cx i) 'CxUniverse) 'CxUniverse M))
      (v/assert kb '(genlCx CxPerfRfR CxUniverse) 'CxUniverse M)
      (doseq [d '[(anti_symmetric pRfAnti) (functional pRfFun) (anti_transitive pRfCh)
                  (arity pRfLen 2)]]
        (v/assert kb d 'CxUniverse M))
      (doseq [i (range (quot n 4))
              :let [a (s "PRfA" i) b (s "PRfB" i) c (s "PRfC" i)]]
        (doseq [t [(list 'pRfAnti a b) (list 'pRfAnti b a) (list 'pRfFun a b) (list 'pRfFun a c)
                   (list 'pRfCh a b) (list 'pRfCh b c) (list 'pRfCh a c)]]
          (v/assert kb t (cx i) {}))
        (v/assert kb (list 'pRfLen a b c) (cx i) M))
      (doseq [j (range 60)] (v/assert kb (list 'pRfFun (s "PRfR" j) 'PRfB) 'CxPerfRfR {})))
    (doall (for [j (range 60)]
             (nanos (let [h (v/assert kb (list 'pRfFun (s "PRfR" j) 'PRfC) 'CxPerfRfR {})]
                      (v/believed? kb h 'CxPerfRfR)))))))

(defn- membership-declaration-arrival
  "One `disjoint` declaration asserted, read through and retracted, over n individuals
  holding one type it separates and n holding the other, beside one individual holding
  both, a `:monotonic` membership and a `:default` one.

  The declaration's arrival reads no membership: the candidate index keeps only a term
  holding two memberships, and the separations are read again over the type pairs the
  kept terms hold (`membership/sync-memberships`), so neither the arrival, its settle nor the
  first read at the pair's context reads a filler (docs/nmtms.md, \"The nogood
  families\")."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pmda_t (symbol (str "PMDA" i))) 'CxPerf {})
        (v/assert kb (list 'pmdb_t (symbol (str "PMDB" i))) 'CxPerf {})))
    (v/assert kb '(pmda_t PMDBoth) 'CxPerf {:strength :monotonic})
    (let [weak (v/assert kb '(pmdb_t PMDBoth) 'CxPerf {})]
      (doall (for [_ (range retract-victims)]
               (nanos (let [d (v/assert kb '(disjoint pmda_t pmdb_t) 'CxPerf
                                        {:strength :monotonic})]
                        (v/believed? kb weak 'CxPerf)
                        (v/retract! kb d))))))))

(defn- decided-warm-read
  "A thousand reads of one self tuple's belief at its context, beside n `:default` self
  tuples an `irreflexive` mark convicts, after the first read at that reader.

  Each self tuple's nogood is placed at its context as a `contradicts` and a `defeat`
  (docs/nmtms.md, \"A nogood placed as a conclusion\"), and no write follows the first
  read.  A read walks the asked handle's support and reads the defeats of each handle by
  target (`exc/defeat-hidden-fn`), so it reads none of the other n nogoods."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(irreflexive pIrrWarm) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [x (symbol (str "PIW" i))]]
        (v/assert kb (list 'pIrrWarm x x) 'CxPerf {})))
    (let [h (v/handle-of kb '(pIrrWarm PIW0 PIW0) 'CxPerf)]
      (v/believed? kb h 'CxPerf)
      (doall (for [_ (range 200)]
               (nanos (dotimes [_ 1000] (v/believed? kb h 'CxPerf))))))))

(defn- arity-exempt-read
  "A thousand reads of one tuple's belief at a context below a second length's binding,
  beside n unrelated predicates each bound to two arguments.

  ```
  CxPerf      (arity pAerHi 2) (genl pAerLo pAerHi) (pAerLo PAEa PAEb PAEc)
   └─ CxAerV  (arity pAerHi 3)
  ```

  The tuple's functor binds no length of its own, and the two lengths above it leave it
  unbound at every context, so the tuple is believed and the two bindings are a pair.
  The read reads no binding, so it reads none of the n unrelated bindings."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/assert kb '(genlCx CxAerV CxPerf) 'CxUniverse M)
    (v/with-deferred-settle kb
      (dotimes [i n] (v/assert kb (list 'arity (symbol (str "pAerU" i)) 2) 'CxPerf M))
      (v/assert kb '(arity pAerHi 2) 'CxPerf M)
      (v/assert kb '(genl pAerLo pAerHi) 'CxPerf M)
      (v/assert kb '(arity pAerHi 3) 'CxAerV M))
    (let [h (v/assert kb '(pAerLo PAEa PAEb PAEc) 'CxPerf {})]
      (v/believed? kb h 'CxAerV)
      (doall (for [_ (range 100)]
               (nanos (dotimes [_ 1000] (v/believed? kb h 'CxAerV))))))))

(defn- firings-beside-a-target
  "`[kb t]`: n standing firings of the forward rule `(fbt_p ?x) ⇒ (fbt_q ?x)` in `CxPerf`,
  and `t`, the handle of one more fact `(fbt_p PFbtT)` stated after them, with each of
  `ctxs` under `CxPerf`."
  [n ctxs]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (doseq [c ctxs] (v/assert kb (list 'genlCx c 'CxPerf) 'CxUniverse M))
    (v/with-deferred-settle kb
      (v/assert kb '(set/forwardRule (implies (fbt_p ?x) (fbt_q ?x))) 'CxPerf M)
      (dotimes [i n] (v/assert kb (list 'fbt_p (symbol (str "PFbt" i))) 'CxPerf M)))
    [kb (v/assert kb '(fbt_p PFbtT) 'CxPerf M)]))

(defn- except-beside-unrelated-firings
  "An `except` of one fact asserted and retracted, beside n standing firings of a forward
  rule that do not rest on the fact.

  ```
  CxPerf     rule (fbt_p ?x) ⇒ (fbt_q ?x)   (fbt_p PFbt0) … (fbt_p PFbt<n-1>)   (fbt_p PFbtT)
   └─ CxEbuD (except (fbt_p PFbtT))
  ```

  The except re-checks the firings resting on its target through any chain
  (`special/recheck-except` over the target's consequence closure), so it reads the one
  firing from `(fbt_p PFbtT)` and none of the other n."
  [n]
  (let [M      {:strength :monotonic}
        [kb t] (firings-beside-a-target n '[CxEbuD])]
    (doall (for [_ (range 60)]
             (nanos (let [e (v/assert kb (list 'except (list 'sentexHandle t)) 'CxEbuD M)]
                      (v/retract! kb e)))))))

(defn- genlcx-edge-beside-seen-excepts
  "A `(genlCx CxGseSub CxGseUp)` edge asserted and retracted, beside n `except`s stated in
  `CxGseHide`, which `CxGseSub` sees before the edge, each of a fact a forward rule fired on.
  With `genlcx-except?`, one more `except`, of a `genlCx` edge between two contexts no
  reader under `CxGseSub` reaches, stated where none reaches.

  ```
  CxPerf          rule (gse_p ?x) ⇒ (gse_q ?x)   (gse_p PGse0) … (gse_p PGse<n-1>)
   └─ CxGseHide   (except (gse_p PGse0)) … (except (gse_p PGse<n-1>))
       ├─ CxGseUp
       └─ CxGseSub
  CxGseFar        (genlCx CxGseNear CxGseFar), excepted in CxGseNear, with genlcx-except?
  ```

  An edge re-checks only the `except`s stated in a context of `super`'s ancestor set that
  `sub` did not see before it (`special/recheck-except-ancestors`).  `CxGseSub` already
  sees every context stating one, so the edge re-checks none of the n.  The excepts in
  force at a reader are read off the raw ancestor set (`tax/context-move`'s raw stratum),
  so an except of a `genlCx` edge elsewhere moves none of that."
  ([n] (genlcx-edge-beside-seen-excepts n false))
  ([n genlcx-except?]
   (let [kb (fresh-kb)
         M  {:strength :monotonic}]
     (v/assert kb '(genlCx CxGseHide CxPerf) 'CxUniverse M)
     (v/assert kb '(genlCx CxGseUp CxGseHide) 'CxUniverse M)
     (v/assert kb '(genlCx CxGseSub CxGseHide) 'CxUniverse M)
     (when genlcx-except?
       (v/assert kb '(genlCx CxGseFar CxUniverse) 'CxUniverse M)
       (let [h (v/assert kb '(genlCx CxGseNear CxGseFar) 'CxUniverse M)]
         (v/assert kb (list 'except (list 'sentexHandle h)) 'CxGseNear M)))
     (v/with-deferred-settle kb
       (v/assert kb '(set/forwardRule (implies (gse_p ?x) (gse_q ?x))) 'CxPerf M)
       (dotimes [i n]
         (let [h (v/assert kb (list 'gse_p (symbol (str "PGse" i))) 'CxPerf M)]
           (v/assert kb (list 'except (list 'sentexHandle h)) 'CxGseHide M))))
     (doall (for [_ (range 60)]
              (nanos (v/retract! kb (v/assert kb '(genlCx CxGseSub CxGseUp) 'CxUniverse M))))))))

(defn- excepts-in-one-settle-beside-excepts
  "16 facts and an `except` of each, asserted under one deferred settle, beside n
  `except`s of facts a forward rule fired on.  The 32 sentexes are retracted, untimed,
  after each reading.

  ```
  CxPerf       rule (esb_p ?x) => (esb_q ?x)   (esb_p PEsb0) … (esb_p PEsb<n-1>)
   └─ CxEsbHide  (except (esb_p PEsb0)) … (except (esb_p PEsb<n-1>))
  ```

  Each write moves the change clock, so the relation gate (`tax/relation-filter-active?`)
  reads the reach again (`kb/supporter-reaches?`), and the reach reads the count of the
  stored excepts and a probe per handle of a supporter's support, not their target set."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        pair (fn [x] (let [h (v/assert kb (list 'esb_p x) 'CxPerf M)]
                       [(v/assert kb (list 'except (list 'sentexHandle h)) 'CxEsbHide M) h]))]
    (v/assert kb '(genlCx CxEsbHide CxPerf) 'CxUniverse M)
    (v/with-deferred-settle kb
      (v/assert kb '(set/forwardRule (implies (esb_p ?x) (esb_q ?x))) 'CxPerf M)
      (dotimes [i n] (pair (symbol (str "PEsb" i)))))
    (doall (for [j (range 60)]
             (let [hs (volatile! nil)
                   t  (nanos (vreset! hs (v/with-deferred-settle kb
                                           (into [] (mapcat #(pair (symbol (str "PEsw" j "x" %))))
                                                 (range 16)))))]
               (run! #(v/retract! kb %) @hs)
               t)))))

(defn- genlcx-edge-revealing-one-except
  "A `(genlCx CxGroSub CxGroHide)` edge asserted and retracted, which shows `CxGroSub` one
  `except`, beside n standing firings of the rule that do not rest on its target.

  ```
  CxPerf         rule (fbt_p ?x) ⇒ (fbt_q ?x)   (fbt_p PFbt0) … (fbt_p PFbt<n-1>)   (fbt_p PFbtT)
   ├─ CxGroHide  (except (fbt_p PFbtT))
   └─ CxGroSub
  ```

  The edge re-checks the firings resting on the `except`'s target and re-joins from that
  target's consequence closure (`special/recheck-except`), so it reads the one firing from
  `(fbt_p PFbtT)` and none of the other n."
  [n]
  (let [M      {:strength :monotonic}
        [kb t] (firings-beside-a-target n '[CxGroHide CxGroSub])]
    (v/assert kb (list 'except (list 'sentexHandle t)) 'CxGroHide M)
    (doall (for [_ (range 60)]
             (nanos (v/retract! kb (v/assert kb '(genlCx CxGroSub CxGroHide) 'CxUniverse M)))))))

(defn- genlcx-edge-beside-stored-context-edges
  "A `(genlCx CxGsdSub CxGsdUp)` edge asserted and retracted, beside n stored `genlCx`
  edges it does not touch and one `except`, of a fact no `genlCx` edge rests on.

  ```
  CxPerf
   ├─ CxGsdUp
   ├─ CxGsdSub
   ├─ CxGsdHide   (except (gsd_p PGsdT))
   └─ CxGsdE0 … CxGsdE<n-1>
  ```

  The reader classes of a `genlCx` move read the contexts stating an `except` that reaches
  a `genlCx` supporter's support (`exc/genlCx-except-contexts`), and the `genlCx` filter
  gate reads whether one does (`exc/genlCx-excepted?`).  Both walk forward from the one
  stored target and read none of the n supporters."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/assert kb '(genlCx CxGsdUp CxPerf) 'CxUniverse M)
    (v/assert kb '(genlCx CxGsdSub CxPerf) 'CxUniverse M)
    (v/assert kb '(genlCx CxGsdHide CxPerf) 'CxUniverse M)
    (v/with-deferred-settle kb
      (dotimes [i n] (v/assert kb (list 'genlCx (pctx "GsdE" i) 'CxPerf) 'CxUniverse M)))
    (let [t (v/assert kb '(gsd_p PGsdT) 'CxPerf M)]
      (v/assert kb (list 'except (list 'sentexHandle t)) 'CxGsdHide M))
    (doall (for [_ (range 60)]
             (nanos (v/retract! kb (v/assert kb '(genlCx CxGsdSub CxGsdUp) 'CxUniverse M)))))))

(defn- deferred-facts-after-a-context-edge
  "The closing settle's drain of `genlCx` moves (`special/drain-context-moves!`) and its
  re-chain (`settle/rechain-seeds`), timed alone, for a deferred batch that asserts a
  `genlCx` edge and then n facts under it, each matched by a forward rule and typed by an
  `arg` declaration stated above the edge.  Each reading wires a context of its own.

  ```
  CxPerf          rule (dfe_p ?x) ⇒ (dfe_q ?x)   (arg dfeLink 1 dfe_thing)
   └─ CxDfe<r>    (dfe_p PDfe<r>N<i>) (dfeLink PDfe<r>N<i> PDfeY), i < n, after the edge
  ```

  Each fact's assert chains it and draws its argument types with the edge in the
  taxonomy, so the drain fetches none of the n: it seeds and sweeps only the facts stored
  below the edge's least believed supporter (`special/seed-floor`).  The rest of the
  settle relabels the n facts and is not timed."
  [n]
  (let [kb    (fresh-kb)
        M     {:strength :monotonic}
        spent (volatile! 0)
        timed (fn [f] (fn [& args]
                        (let [t (System/nanoTime)]
                          (try (apply f args) (finally (vswap! spent + (- (System/nanoTime) t)))))))]
    (v/assert kb '(set/forwardRule (implies (dfe_p ?x) (dfe_q ?x))) 'CxPerf M)
    (v/assert kb '(genl dfe_thing thing) 'CxPerf M)
    (v/assert kb '(arg dfeLink 1 dfe_thing) 'CxPerf M)
    (with-redefs [special/drain-context-moves! (timed special/drain-context-moves!)
                  settle/rechain-seeds         (timed settle/rechain-seeds)]
      (doall (for [r (range 20)]
               (let [c (pctx "Dfe" r)]
                 (v/with-deferred-settle kb
                   (v/assert kb (list 'genlCx c 'CxPerf) 'CxUniverse M)
                   (dotimes [i n]
                     (let [x (symbol (str "PDfe" r "N" i))]
                       (v/assert kb (list 'dfe_p x) c M)
                       (v/assert kb (list 'dfeLink x 'PDfeY) c M)))
                   ;; the batch's asserts are not timed: only the closing settle's drain
                   ;; and re-chain, which run after the body
                   (vreset! spent 0))
                 @spent))))))

(defn- except-of-a-guard-blocker
  "An `except` of the fact that blocks one firing of an `exceptWhen` rule, asserted and
  retracted, beside n firings of the rule that the fact does not block.

  ```
  CxPerf   rule (pxg_bird ?x) exceptWhen (pxg_penguin ?x) ⇒ (pxg_flies ?x)
           (pxg_bird PXG0) … (pxg_bird PXG<n-1>)   (pxg_bird PXGT)   (pxg_penguin PXGT)
           (except (pxg_penguin PXGT))
  ```

  The except hides the blocker, so the blocker's sentence queues the rule
  (`special/recheck-except`) and the settle releases the firing the blocker swept from
  the refusal record (`chain/record-swept-firing!`).  Retracting the except blocks it
  again.  A re-chain of the rule over its extent reads here as growth."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (v/assert kb '(exceptWhen (pxg_penguin ?x) (set/forwardRule (implies (pxg_bird ?x) (pxg_flies ?x))))
                'CxPerf)
      (dotimes [i n] (v/assert kb (list 'pxg_bird (symbol (str "PXG" i))) 'CxPerf)))
    (v/assert kb '(pxg_bird PXGT) 'CxPerf)
    (let [t (v/assert kb '(pxg_penguin PXGT) 'CxPerf)]
      (doall (for [_ (range 60)]
               (nanos (let [e (v/assert kb (list 'except (list 'sentexHandle t)) 'CxPerf)]
                        (v/retract! kb e))))))))

(defn- guard-defeats-at-a-reader
  "One firing of an `exceptWhen` rule, its blocker stated in each of n contexts below the
  rule's, so n guard defeats name the firing, and a reader below all n.

  ```
  CxPgTop   rule (pgr_bird ?x) exceptWhen (pgr_pen ?x) ⇒ (pgr_flies ?x)   (pgr_bird PGR)
  CxPgSub<i> ⊂ CxPgTop                                    (pgr_pen PGR)
  CxPgReader ⊂ each CxPgSub<i>
  ```

  Each reading is one `believed?` of the firing at the reader, after a fact the reader
  sees is asserted and retracted, so no read memo holds the answer.  A guard defeat's read
  reading the firing's guard coverage, which reads every guard defeat of the firing
  again, reads here as growth in the factorial of n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/assert kb '(genlCx CxPgTop CxUniverse) 'CxUniverse M)
    (v/assert kb '(exceptWhen (pgr_pen ?x) (set/forwardRule (implies (pgr_bird ?x) (pgr_flies ?x))))
              'CxPgTop)
    (v/assert kb '(pgr_bird PGR) 'CxPgTop)
    (dotimes [i n]
      (let [c (symbol (str "CxPgSub" i))]
        (v/assert kb (list 'genlCx c 'CxPgTop) 'CxUniverse M)
        (v/assert kb '(pgr_pen PGR) c)
        (v/assert kb (list 'genlCx 'CxPgReader c) 'CxUniverse M)))
    (let [h (v/handle-of kb '(pgr_flies PGR) 'CxPgTop)]
      (doall (for [i (range 20)]
               (let [e (v/assert kb (list 'pgr_other (symbol (str "PGRO" i))) 'CxPgReader)]
                 (v/retract! kb e)
                 (nanos (v/believed? kb h 'CxPgReader))))))))

(defn- source-datum-beside-computed-firings
  "A `length` fact, asserted and retracted, on a KB holding n firings of a rule whose
  antecedent the quantity prover answers.

  ```
  CxPerf   rule (pscMass ?x ?q) ∧ (quantityGreaterThan ?q (QuantityFn 1 Kilogram)) ⇒ (psc_heavy ?x)
           (pscMass PSC0 (QuantityFn 2 Kilogram)) … (pscMass PSC<n-1> …)
  timed    (length PSCL<i> (QuantityFn 1 Hour)) asserted and retracted
  ```

  With the duration prover registered, `length` is a source of it and not of the
  quantity prover, so the datum moves no answer a firing of the rule rests on: the write
  re-checks and re-joins none of them (`special/computed-reading-rules`).  A re-check or
  re-join of the rule over its firings reads here as growth."
  [n]
  (let [kb (v/add-reasoner (fresh-kb) :duration)]
    (v/with-deferred-settle kb
      (v/assert kb '(set/forwardRule
                     (implies (and (pscMass ?x ?q) (quantityGreaterThan ?q (QuantityFn 1 Kilogram)))
                              (psc_heavy ?x)))
                'CxPerf)
      (dotimes [i n]
        (v/assert kb (list 'pscMass (symbol (str "PSC" i)) '(QuantityFn 2 Kilogram)) 'CxPerf)))
    (doall (for [i (range 60)]
             (nanos (v/retract! kb (v/assert kb (list 'length (symbol (str "PSCL" i))
                                                      '(QuantityFn 1 Hour))
                                             'CxPerf)))))))

(defn- held-shape-first-withdrawal
  "A read of one of 200 `:default` self tuples under an `irreflexive` mark, which a placed
  defeat takes OUT at the reader, beside n ternary tuples of a predicate bound to three
  arguments under one bound to two.

  A length above the functor differs from the tuples' length, and the functor's own
  binding holds them, so they are not inert and the read walk reads none of them
  (docs/nmtms.md, \"A nogood placed as a conclusion\").  A
  read reading every candidate tuple reads here as growth."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/assert kb '(genlCx CxPerfHsR CxPerf) 'CxUniverse M)
    (v/with-deferred-settle kb
      (v/assert kb '(irreflexive pHsSelf) 'CxPerf M)
      (dotimes [i 200]
        (let [x (symbol (str "PHsS" i))] (v/assert kb (list 'pHsSelf x x) 'CxPerf {})))
      (v/assert kb '(arity pHsHi 2) 'CxPerf M)
      (v/assert kb '(arity pHsLo 3) 'CxPerf M)
      (v/assert kb '(genl pHsLo pHsHi) 'CxPerf M)
      (dotimes [i n]
        (v/assert kb (list 'pHsLo (symbol (str "PHsA" i)) 'PHsB 'PHsC) 'CxPerf {})))
    (let [h (v/handle-of kb '(pHsSelf PHsS0 PHsS0) 'CxPerf)]
      (doall (for [_ (range 100)]
               (nanos (v/believed? kb h 'CxPerfHsR)))))))

(defn- negation-reader-kb
  "A KB holding n negation pairs placed at `CxPNJ`: `(pnr_i PNR_i)` in `CxPNL` and its
  denial in `CxPNR`, both `:default`, which `CxPNJ` sees both of.  Built under one deferred
  settle and read once at `CxPNJ`."
  [n]
  (let [kb (fresh-kb)]
    (doseq [[c up] '[[CxPNL CxUniverse] [CxPNR CxUniverse] [CxPNJ CxPNL] [CxPNJ CxPNR]
                     [CxPNU CxUniverse]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse {:strength :monotonic}))
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [s (list (symbol (str "pnr" i)) (symbol (str "PNR" i)))]]
        (v/assert kb s 'CxPNL {})
        (v/assert kb (list 'not s) 'CxPNR {})))
    (v/believed? kb (v/handle-of kb '(pnr0 PNR0) 'CxPNL) 'CxPNJ)
    kb))

(defn- negation-reader-write
  "An assert of a fact naming nothing, in a context that sees neither side, beside n
  negation pairs placed at one reader (`negation-reader-kb`).

  The settle places none of the pairs again, since the fact moves no pair's member, no
  index entry and no stamp (docs/nmtms.md, \"The nogood families\")."
  [n]
  (let [kb (negation-reader-kb n)]
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pnr_unrel (symbol (str "PNU" i))) 'CxPNU {}))))))

(defn- negation-pairs-kb
  "A KB holding n negation pairs in CxUniverse, `(pnq_i PNQ_i)` `:default` and its denial
  `:monotonic`, each placed with its `defeat`.  Built under one deferred settle."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [s (list (symbol (str "pnq" i)) (symbol (str "PNQ" i)))]]
        (v/assert kb s 'CxUniverse {})
        (v/assert kb (list 'not s) 'CxUniverse {:strength :monotonic})))
    kb))

(defn- recover-negation-pairs
  "One `recover` of `negation-pairs-kb`, divided by n.  The recover's closing settle
  places the bodies the rebuilt candidate index queued (`chain/placement-queued?`)."
  [n]
  (let [kb (negation-pairs-kb n)]
    (doall (for [_ (range 3)] (quot (nanos (v/recover kb)) n)))))

(defn- witness-walk-beside-side-ancestors
  "One `genl` witness walk (`tax/reach-support`, with the defeat class) from a type up a
  chain of L+2 edges to a root, where the type's other parent heads a binary tree of n
  types, L levels deep, none of them under the root.  A breadth-first walk would expand
  every tree type before the root; the walk expands a type off the root's down-closure
  only among its first expansions."
  [n]
  (let [kb  (fresh-kb)
        tx  (reasoning/taxonomy kb)
        tms (reasoning/tms kb)
        lv  (long (Math/ceil (/ (Math/log (inc n)) (Math/log 2))))
        sd  (fn [i] (symbol (str "wwb_side_" i "_kind")))
        ch  (fn [i] (symbol (str "wwb_chain_" i "_kind")))]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl 'wwb_sub_kind (sd 0)) 'CxPerf {})
      (dotimes [i n]
        (doseq [c [(inc (* 2 i)) (+ 2 (* 2 i))] :when (< c n)]
          (v/assert kb (list 'genl (sd i) (sd c)) 'CxPerf {})))
      (v/assert kb (list 'genl 'wwb_sub_kind (ch 0)) 'CxPerf {})
      (dotimes [i lv] (v/assert kb (list 'genl (ch i) (ch (inc i))) 'CxPerf {}))
      (v/assert kb (list 'genl (ch lv) 'wwb_top_kind) 'CxPerf {}))
    (doall (for [_ (range 60)]
             (nanos (tax/reach-support tx :genl 'wwb_sub_kind 'wwb_top_kind 'CxPerf
                                       #(jtms/defeat-class tms %)))))))

(defn- recover-placement-walk
  "One settle placing the nogoods a candidate index rebuilt as `recover` rebuilds it
  queued (`decide/rebuild-candidates!`, the settle `recover` closes with), divided by the
  nogoods: 1600 terms, each in a leaf type under each of two `disjoint` roots, over a
  layered `genl` graph per root of nine levels of w types (0 to 8), each type below level
  0 under up to three types of the level above.  Four leaves per root, so the 1600
  nogoods climb eight subsumptions, each through the w·8 types above its leaf.

  The settle walks each subsumption once per vantage, so the walk is paid eight times
  and not once per nogood.  The eight walks grow with w, and the 1600 nogoods divide
  their share of each nogood's cost."
  [w]
  (let [kb   (fresh-kb)
        nn   1600
        rnd  (java.util.Random. 48)
        M    {:strength :monotonic}
        node (fn [side i j] (symbol (str "rpw" side "_" i "_" j "_kind")))
        top  (fn [side] (symbol (str "rpw" side "_kind")))]
    (v/with-deferred-settle kb
      (v/assert kb (list 'disjoint (top "a") (top "b")) 'CxPerf M)
      (doseq [side ["a" "b"]]
        (dotimes [j w] (v/assert kb (list 'genl (node side 0 j) (top side)) 'CxPerf {}))
        (doseq [i (range 1 9) j (range w) pj (distinct (repeatedly 3 #(.nextInt rnd (int w))))]
          (v/assert kb (list 'genl (node side i j) (node side (dec i) pj)) 'CxPerf
                    (if (zero? (.nextInt rnd 3)) M {}))))
      (dotimes [x nn]
        (let [t (symbol (str "RPW" x))]
          (v/assert kb (list (node "a" 8 (mod x 4)) t) 'CxPerf {})
          (v/assert kb (list (node "b" 8 (mod (quot x 4) 4)) t) 'CxPerf {}))))
    (doall (for [_ (range 12)]
             (do (decide/rebuild-candidates! kb)
                 (quot (nanos (settle/settle kb)) nn))))))

(defn- first-write-after-recover
  "The first assert after a `recover` of `negation-pairs-kb`, of a fact naming nothing.
  The recover placed every pair, so the write places none of them."
  [n]
  (let [kb (negation-pairs-kb n)]
    (doall (for [i (range 30)]
             (do (v/recover kb)
                 (nanos (v/assert kb (list 'pnq_unrel (symbol (str "PNQU" i))) 'CxUniverse {})))))))

(defn- tuple-mark-determinant-write
  "100 ternary tuples asserted under `(functionalInArg P 3)`, each on a determinant of its
  own, `(P PTAh PTBh' v)` for hubs h and h' of ten, beside n stored tuples on n other
  determinants: half `(P PTAh PTXi i)` and half `(P PTYi PTBh i)`, so each hub's argument
  root holds n/20 tuples and neither argument of a new determinant narrows the read alone.

  A tuple reads the stored tuples of its own determinant, one trie read of `(P a b ?v)`
  (`tuple/note-tuple!`), and neither argument's posting nor the predicate's extent, so
  the write is flat in n (docs/nmtms.md, \"The nogood families\")."
  [n]
  (let [kb  (fresh-kb)
        hub (fn [c i] (symbol (str c (mod i 10))))]
    (v/assert kb '(functionalInArg pTripleDet 3) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (if (even? i)
                       (list 'pTripleDet (hub "PTA" (quot i 2)) (symbol (str "PTX" i)) i)
                       (list 'pTripleDet (symbol (str "PTY" i)) (hub "PTB" (quot i 2)) i))
                  'CxPerf {})))
    (doall
     (for [i (range 100)]
       (nanos (v/assert kb (list 'pTripleDet (hub "PTA" i) (hub "PTB" (quot i 10)) i)
                        'CxPerf {}))))))

(defn- assert-over-standing-excepts
  "One assert of a fact naming nothing, on a KB carrying n believed `(except
  (sentexHandle H))` facts, each hiding a decoy the fact does not name.

  The timed operation is an ordinary assert and its own settle, and that is the arm
  `visibility-reading` does not take: that check times a read, and this one times the
  write, whose settle places nothing the assert does not reach (docs/nmtms.md, \"A
  nogood placed as a conclusion\").  The population is built under one deferred
  settle, which settles before the first reading."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [h (v/assert kb (list 'pv_decoy (symbol (str "PVD" i))) 'CxPerf
                                {:strength :monotonic})]]
        (v/assert kb (list 'except (sx/sentex-handle h)) 'CxPerf {:strength :monotonic})))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pStandVictim (symbol (str "PSV" i)) 'PSVal)
                              'CxPerf {}))))))

(defn- assert-beside-naf-refusals
  "One assert of a fact naming nothing, on a KB whose 16 `unknown` rules hold n refused
  firings between them in the refusal record.

  Every settle pass asks the record for the lifts, the mints and the argument
  convictions waiting in it (`settle/released-lifts`, `released-mints`,
  `released-constraint-refusals`), and the KB holds none of the three: what the
  unrelated assert owes the record is nothing at both sizes.  The population is built
  under one deferred settle, with each blocking fact stored before the firing it
  refuses."
  [n]
  (let [kb    (fresh-kb)
        rules 16]
    (v/with-deferred-settle kb
      (doseq [r (range rules)
              :let [in  (symbol (str "pnrIn" r))
                    blk (symbol (str "pnrBlock" r))]]
        (v/assert kb (list 'implies (list 'and (list in '?x '?y)
                                          (list 'unknown (list blk '?x '?y)))
                           (list (symbol (str "pnrOut" r)) '?x '?y))
                  'CxPerf {:direction :forward})
        (doseq [i (range (quot n rules))
                :let [x (symbol (str "PNR" r "x" i))]]
          (v/assert kb (list blk x 'PNRVal) 'CxPerf {})
          (v/assert kb (list in x 'PNRVal) 'CxPerf {}))))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pnrVictim (symbol (str "PNRV" i)) 'PNRVal)
                              'CxPerf {}))))))

(defn- released-refusal-beside-guarded-firings
  "One `retract!` of the fact an `unknown` rule's refused firing waited on, on a KB whose
  `exceptWhen` rule holds n firings.  The released firing places a sentence the exception
  reads, so the pass queues the `exceptWhen` rule for a re-check.

  The re-check is owed to the next pass, which re-decides the rule's firings against the
  queued sentence (`recheck/exception-candidates`); re-joining the rule over its n
  antecedent facts in the pass that queued it would be a second answer to the same
  question (docs/exceptions.md, \"Re-chaining what was released, not what was
  touched\")."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (v/assert kb '(exceptWhen (prr_penguin ?x) (set/forwardRule (implies (prr_bird ?x) (prr_flies ?x))))
                'CxPerf)
      (v/assert kb '(set/forwardRule (implies (and (prr_polar ?x) (unknown (prr_tropic ?x)))
                                              (prr_penguin ?x)))
                'CxPerf)
      (doseq [i (range n)]
        (v/assert kb (list 'prr_bird (symbol (str "PRB" i))) 'CxPerf)))
    (doall
     (for [i (range 60)
           :let [x (symbol (str "PRX" i))]]
       (do (v/assert kb (list 'prr_bird x) 'CxPerf)
           (v/assert kb (list 'prr_tropic x) 'CxPerf)
           (v/assert kb (list 'prr_polar x) 'CxPerf)
           (let [h (v/handle-of kb (list 'prr_tropic x) 'CxPerf)]
             (nanos (v/retract! kb h))))))))

(defn- guarded-firings-read-below
  "The first read, at a context below an `exceptWhen` rule's, of a firing placed after n
  others, where that context sees no fact the exception reads.

  A guard that holds below a firing's placement stores a guard `defeat` there
  (docs/naf.md, \"Evaluated in the placement context, not the join\"), and a reader
  that sees no blocker sees none, so the read walk meets none of the n."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genlCx CxPerfGR CxPerf) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      (v/assert kb '(exceptWhen (pgr_penguin ?x) (set/forwardRule (implies (pgr_bird ?x) (pgr_flies ?x))))
                'CxPerf)
      (doseq [i (range n)]
        (v/assert kb (list 'pgr_bird (symbol (str "PGRB" i))) 'CxPerf)))
    (v/assert kb '(pgr_other PGRO) 'CxPerfGR)
    (doall
     (for [i (range 60)
           :let [x (symbol (str "PGRX" i))]]
       (do (v/assert kb (list 'pgr_bird x) 'CxPerf)
           (let [h (v/handle-of kb (list 'pgr_flies x) 'CxPerf)]
             (nanos (v/believed? kb h 'CxPerfGR))))))))

(defn- unmerge-over-standing-merges
  "One `retract!` of a `sameAs` merge that displaces one fact of its own, on a KB
  carrying n standing merges that each displace one fact.

  The un-merge moves the equality closure, so its settle gives the displaced spelling
  back.  The n standing merges are disjoint from every victim: what the retraction owes
  is its own class and its own fact at both sizes, and the reading tracks what the
  supersession reconcile walks beyond that."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pMergeBorn (symbol (str "PMHi" i)) 'PMPlace) 'CxPerf {})
        (v/assert kb (list 'sameAs (symbol (str "PMAa" i)) (symbol (str "PMHi" i)))
                  'CxPerf {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pMergeBorn (symbol (str "PXHi" i)) 'PMPlace)
                                    'CxPerf {})
                          (v/assert kb (list 'sameAs (symbol (str "PXAa" i)) (symbol (str "PXHi" i)))
                                    'CxPerf {}))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))

(defn- deferred-merge-batch
  "One merging assert inside a `with-deferred-settle` batch, read at the tail of a batch of
  n merges that each displace one fact.

  The batch's touched window spans every write in it, and the write path's supersession
  reconcile examines migration's output and the classes it moved
  (`special/refresh-supersessions`).  A reconcile that read the window per merge would
  re-examine every entry the batch had displaced so far, and the k-th merge would cost
  O(k)."
  [n]
  (let [kb (fresh-kb)
        ts (volatile! [])]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pMergeBorn (symbol (str "PDHi" i)) 'PMPlace) 'CxPerf {})
        (vswap! ts conj (nanos (v/assert kb (list 'sameAs (symbol (str "PDAa" i))
                                                  (symbol (str "PDHi" i)))
                                         'CxPerf {})))))
    @ts))

(defn- merge-withdrawing-a-firing
  "One merging assert whose displaced fact fired a forward rule before the merge, on a KB
  carrying n standing merges whose displaced facts each fired the same rule.

  The settle drops each firing over a spelling the merge supersedes
  (`settle/withdraw-retired-firings!`), reading the dependents of the spellings this
  settle superseded: one fact and its firing at both sizes, and none of the n standing
  merges' spellings."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(implies (pWdBorn ?x ?p) (pWdDerived ?x ?p)) 'CxPerf {:direction :forward})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pWdBorn (symbol (str "PWHi" i)) 'PWPlace) 'CxPerf {})
        (v/assert kb (list 'sameAs (symbol (str "PWAa" i)) (symbol (str "PWHi" i))) 'CxPerf {})))
    (doall (for [i (range retract-victims)]
             (do (v/assert kb (list 'pWdBorn (symbol (str "PWXHi" i)) 'PWPlace) 'CxPerf {})
                 (nanos (v/assert kb (list 'sameAs (symbol (str "PWXAa" i)) (symbol (str "PWXHi" i)))
                                  'CxPerf {})))))))

(def ^:private edge-writes
  "Taxonomy edges written per run, for the same reason `retract-victims` is what it is: an
  edge handle can only be written once, so the timed operation needs a supply of distinct
  edges, and there have to be more of them than `tail-samples` takes.  **The same count at
  both sizes**, so each answer is the mean of the last fifty over windows of equal width,
  and each edge is its own fresh pair of terms — re-asserting an active edge is a no-op
  that bumps no generation and would time nothing."
  60)

(defn- edge-beside-contradicted-orthogonals
  "One `genl` edge and one `disjoint` over fresh types, beside n `orthogonal`s each over two
  subtypes of a separated pair, so the KB carries n placed one-member clashes.

  The related-types index reads an `orthogonal` again only where its argument's ancestor
  set moved, or where the settle relabels a separation over a type at or above one of its
  arguments (`related/reread-separated!`), so neither write reads a standing `orthogonal`
  or places one again (docs/nmtms.md, \"Declarations over related types\")."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (v/assert kb '(genl porthua_t thing) 'CxPerf {:strength :monotonic})
      (v/assert kb '(genl porthub_t thing) 'CxPerf {:strength :monotonic})
      (v/assert kb '(disjoint porthua_t porthub_t) 'CxPerf {:strength :monotonic})
      (doseq [i (range n)]
        (let [a (symbol (str "porthsa" i "_t")) b (symbol (str "porthsb" i "_t"))]
          (v/assert kb (list 'genl a 'porthua_t) 'CxPerf {:strength :monotonic})
          (v/assert kb (list 'genl b 'porthub_t) 'CxPerf {:strength :monotonic})
          (v/assert kb (list 'orthogonal a b) 'CxPerf {:strength :monotonic}))))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl (symbol (str "porthe" i "_t")) 'thing)
                              'CxPerf {:strength :monotonic})
                    (v/assert kb (list 'disjoint (symbol (str "porthe" i "_t"))
                                       (symbol (str "porthf" i "_t")))
                              'CxPerf {:strength :monotonic}))))))

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

(defn- converse-tuple-beside-tuples
  "An assert of a tuple `(pct a b)` under an `anti_symmetric` mark, beside n stored `pct`
  tuples, none of them its converse.

  The converse family reads the converse the tuple's own arguments name, one trie read of
  `(pct b a)` per converse functor (`tuple/stored-converses`), and keeps no stored tuple;
  a read that walked the functor's tuples, or the tuples sharing an argument, grows with n."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(anti_symmetric pct) 'CxPerf {:strength :monotonic})
    (v/bulk-assert-facts! kb (for [i (range n)] (list 'pct 'PCTA (symbol (str "PCTB" i))))
                          'CxPerf)
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pct (symbol (str "PCTC" i)) 'PCTA) 'CxPerf {}))))))

(defn- negation-gate-denials
  "An assert of a fact naming nothing, beside n negative facts with no positive twin.

  Each settle asks whether any body is stored in both polarities before it places a
  negation pair (`chain/place-nogoods!`).  The opposed family answers with one count read
  (`reads/stores-opposed?`); a walk over the denied bodies under `[:false]` costs one
  step per denial, per settle."
  [n]
  (let [kb (fresh-kb)]
    (v/bulk-assert-facts! kb (for [i (range n)] (list 'not (list 'pgd_t (symbol (str "PGD" i)))))
                          'CxPerf)
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pgd_unrel (symbol (str "PGU" i))) 'CxPerf {}))))))

(defn- genl-cx-edge-beside-opposed
  "One `genlCx` edge putting a fresh context under `CxPGX`, beside n bodies stored in both
  polarities, `(pgo_t PGOi)` in `CxPGL` and its denial in `CxPGR`, contexts the edge does
  not reach.

  The edge exposes `CxPGX` to the fresh context, so the placement pass reads the negation
  members stated there (`special/drain-context-moves!`' `:reach`, its `:below`).  The
  opposed family keys them by context first (`[:opposed-in ctx]`), one leaf read per
  exposed context; keyed context last, the read visits every opposed body."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (doseq [c '[CxPGL CxPGR CxPGX]]
      (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse m))
    (v/bulk-assert-facts! kb (for [i (range n)] (list 'pgo_t (symbol (str "PGO" i)))) 'CxPGL)
    (v/bulk-assert-facts! kb (for [i (range n)] (list 'not (list 'pgo_t (symbol (str "PGO" i)))))
                          'CxPGR)
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genlCx (symbol (str "CxPGE" i)) 'CxPGX) 'CxUniverse m))))))

(defn- genl-edge-under-no-merge-mark
  "One `genl` edge above a type whose spec subtree holds n exact-arity memberships, on a
  KB declaring a `functional` and an `anti_symmetric` mark on predicates the edge does not
  reach.  Each timed edge puts the same type under a fresh supertype.

  The two merge arms (`special/equate-under-edge`, `special/antisym-equate-under-edge`)
  derive over the subtree only when a mark of their family stands over the edge's upper
  end.  An arm gated on the mark being declared anywhere reads every fact of the subtree
  per edge, and the antisymmetric one offers each back to the candidate index, where a
  membership queues its predicate's shapes for the inert-tuple refresh.  Written
  unchained, so the
  reading is the two arms' alone."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(functional pgmFn) 'CxPerf m)
    (v/assert kb '(anti_symmetric pgmAnti) 'CxPerf m)
    (v/assert kb '(genl binary_predicate pgm_rel) 'CxPerf m)
    (dotimes [i n]
      (v/assert kb (list 'binary_predicate (symbol (str "pgmRel" i))) 'CxPerf m))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl 'pgm_rel (symbol (str "pgm_top" i)))
                              'CxPerf {:strength :monotonic :chain? false}))))))

(defn- genl-edge-under-no-rule-above
  "One `genl` edge above a type holding n members, on a KB whose one forward rule reads a
  type the edge does not reach.  Each timed edge puts the same type under a fresh
  supertype, chained.

  `special/subsumption-seeds` puts the facts below an edge back on the chaining agenda
  only when a rule reads a term at or above the edge's upper end.  Seeding them on every
  edge sends all n to the agenda per edge, each to find no rule it newly reaches."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(set/forwardRule (implies (pgr_else ?x) (pgr_seen ?x))) 'CxPerf m)
    (dotimes [i n]
      (v/assert kb (list 'pgr_low (symbol (str "PGR" i))) 'CxPerf m))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl 'pgr_low (symbol (str "pgr_top" i))) 'CxPerf m))))))

(defn- genl-edge-beside-arity-conflicts
  "One `genl` edge putting a fresh type under the bottom of a chain of eight types bound to
  one argument, beside n predicates under an arity conflict in a context the edge's does
  not see: each binds one argument under a root binding two.

  ```
  CxUniverse
   ├─ CxPerfGacSide  (genl pgacRel_i pgacRoot) (arity pgacRel_i 1), (arity pgacRoot 2)
   └─ CxPerfGacEdge  the chain pgac7_t < … < pgac0_t, (arity pgac0_t 1)
                     timed  (genl pgacv_j_t pgac7_t)
  ```

  The edge brings the chain's length to its lower end, and the settle's refresh reads the
  functors at or below that end and the pairs above it (`arity/drain!`,
  `arity/pair-sets`), none of which is under the conflict.  Asking each functor under a
  conflict whether it reaches the lower end is one reachability walk per functor per
  edge."
  [n]
  (let [kb    (fresh-kb)
        m     {:strength :monotonic}
        chain (fn [i] (symbol (str "pgac" i "_t")))]
    (v/with-deferred-settle kb
      (doseq [c '[CxPerfGacSide CxPerfGacEdge]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse m))
      (v/assert kb '(arity pgacRoot 2) 'CxPerfGacSide m)
      (dotimes [i n]
        (let [p (symbol (str "pgacRel" i))]
          (v/assert kb (list 'genl p 'pgacRoot) 'CxPerfGacSide m)
          (v/assert kb (list 'arity p 1) 'CxPerfGacSide m))))
    (doseq [i (range 1 8)]
      (v/assert kb (list 'genl (chain i) (chain (dec i))) 'CxPerfGacEdge m))
    (v/assert kb (list 'arity (chain 0) 1) 'CxPerfGacEdge m)
    ;; the assert alone is timed, its settle deferred past the reading: a reader re-reading
    ;; the arity pairs is the settle's cost, and this check is about the arrival's
    (doall (for [i (range edge-writes)]
             (let [t (volatile! 0)]
               (v/with-deferred-settle kb
                 (vreset! t (nanos (v/assert kb (list 'genl (symbol (str "pgacv" i "_t")) (chain 7))
                                             'CxPerfGacEdge m))))
               @t)))))

(defn- edge-stratification-walk
  "The stratification check of one `genl` edge that closes a positive cycle through a
  chain of eight rules, rule i reading `pswlink<i>_t` and concluding `pswlink<i+1>_t`, with
  n spec types under every link.  One excepted rule elsewhere keeps the check walking.

  The check is `checks/edge-stratification-violation`, which asks without writing, so
  every sample asks the same edge.  Its walk (`wff/genl-negation-cycle`) reaches the eight
  rules, and from each reads the upward closure of its consequent and the rule index under
  each predicate in it.  A walk fanning each read predicate's spec closure reads the rule
  index under every one of the n specs per rule (docs/exceptions.md, \"The search\")."
  [n]
  (let [kb    (fresh-kb)
        links (mapv #(symbol (str "pswlink" % "_t")) (range 9))]
    (doseq [t links, j (range n)]
      (v/assert kb (list 'genl (symbol (str (name t) "kind" j "_t")) t)
                'CxPerf {:strength :monotonic}))
    (doseq [[t u] (partition 2 1 links)]
      (v/assert kb (list 'implies (list 'and (list t '?x)) (list u '?x))
                'CxPerf {:direction :forward}))
    (v/assert kb '(exceptWhen (pswexc ?x)
                              (set/defaultRule (implies (and (pswbase ?x)) (pswseen ?x))))
              'CxPerf {})
    (let [edge (list 'genl (peek links) (first links))]
      (doall (for [_ (range edge-writes)]
               (nanos (checks/edge-stratification-violation kb edge)))))))

(defn- edge-stratification-unreached
  "One `genl` edge under `psutop_t`, on a KB holding n excepted rules the edge does not
  reach.

  Eight rules read `psutop_t` and conclude predicates no rule reads.  Eight spokes sit
  under `psuhub_t`, eight rules read the hub and conclude a spoke each, and the n excepted
  rules read the hub too.  The timed edge puts a fresh subtype under `psutop_t`: its
  stratification walk (`wff/genl-negation-cycle`) starts at the eight readers of
  `psutop_t` and reaches nothing else, whatever n is.  A walk from every excepted rule
  expands n + 8 rules per start, n times over."
  [n]
  (let [kb     (fresh-kb)
        spokes (mapv #(symbol (str "psuspoke" % "_t")) (range 8))]
    (doseq [[i t] (map-indexed vector spokes)]
      (v/assert kb (list 'genl t 'psuhub_t) 'CxPerf {:strength :monotonic})
      (v/assert kb (list 'implies (list 'and (list 'psuhub_t '?x)) (list t '?x))
                'CxPerf {:direction :forward})
      (v/assert kb (list 'implies (list 'and (list 'psutop_t '?x))
                         (list (symbol (str "psuout" i "_t")) '?x))
                'CxPerf {:direction :forward}))
    (doseq [i (range n)]
      (v/assert kb (list 'exceptWhen (list (symbol (str "psuexc" i "_t")) '?x)
                         (list 'set/defaultRule
                               (list 'implies (list 'and (list 'psuhub_t '?x))
                                     (list (symbol (str "psuseen" i "_t")) '?x))))
                'CxPerf {}))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl (symbol (str "psusub" i "_t")) 'psutop_t)
                              'CxPerf {:strength :monotonic}))))))

(defn- edge-stratification-subsumed
  "The stratification check of one `genl` edge from `psssub_t` to `psstop_t`, which a
  stored chain through `pssmid_t` already connects, beside n excepted rules reading
  `psstop_t`.

  The check is `checks/edge-stratification-violation`, which asks without writing, so
  every sample asks the same edge.  The edge moves no closure, so it adds no edge to the
  rule dependency graph and the check stops at one reachability test.  A walk from each
  rule reading a predicate above the upper end expands the n excepted rules."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl psssub_t pssmid_t) 'CxPerf {:strength :monotonic})
    (v/assert kb '(genl pssmid_t psstop_t) 'CxPerf {:strength :monotonic})
    (doseq [i (range n)]
      (v/assert kb (list 'exceptWhen (list (symbol (str "pssexc" i "_t")) '?x)
                         (list 'set/defaultRule
                               (list 'implies (list 'and (list 'psstop_t '?x))
                                     (list (symbol (str "pssseen" i "_t")) '?x))))
                'CxPerf {}))
    (doall (for [_ (range edge-writes)]
             (nanos (dotimes [_ reads-per-reading]
                      (checks/edge-stratification-violation kb '(genl psssub_t psstop_t))))))))

(defn- taxonomy-edge-arbitration
  "One `genl` edge — a fresh subtype under a fresh supertype, with nothing above it,
  nothing below it and no separation anywhere near it — written on a KB carrying n
  standing definitional dilemmas.

  `clash-arbitration` builds that standing set and then never writes a taxonomy edge, so
  the whole of its run reads one clash vocabulary and the memo's staleness test is never
  asked a question.  This is the workload that asks it.  Every edge activation bumps the
  relation's generation, and each standing dilemma is a membership nogood placed where it
  is seen whole (docs/nmtms.md, \"The nogood families\"), so an edge that separates
  nothing and reaches no instance moves none of them.

  The KB also carries a `sibling_disjoint` mark with nothing under it.  A sibling
  separation reads the `genl` edges between two supertypes, and a memo that re-derived
  every standing pair while such a mark stands would read the retired-memo shape here.

  The dilemmas are built under one deferred settle: the standing set is the KB this
  measures against and not the thing being measured."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(disjoint pea_t peb_t) 'CxPerf {:strength :monotonic})
    (v/assert kb '(sibling_disjoint pesib_t) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [x (symbol (str "PEX" i))]]
        (v/assert kb (list 'pea_t x) 'CxPerf {})
        (v/assert kb (list 'peb_t x) 'CxPerf {})))
    (doall
     (for [i (range edge-writes)]
       (nanos (v/assert kb (list 'genl (symbol (str "pev" i "_t"))
                                 (symbol (str "peu" i "_t")))
                        'CxPerf {:strength :monotonic}))))))

(defn- context-edge-arbitration
  "One `genlCx` edge — a fresh context under `CxUniverse`, with nothing below it —
  written on a KB carrying n standing `:default` P/¬P dilemmas in `CxPerf`, which the
  edge does not reach.

  The negation twin of `taxonomy-edge-arbitration`: `negation-arbitration` builds the
  same standing set and writes no context edge afterwards.  Joint visibility is read
  through the `genlCx` closure, so a read of the opposed bodies keyed on that closure's
  generation re-derives every standing pair per edge.  No separation is stated, so this
  times the negation pairing alone.  The dilemmas are built under one deferred settle."
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
       (nanos (v/assert kb (list 'genlCx (symbol (str "CxPCtx" i)) 'CxUniverse)
                        'CxPerf {:strength :monotonic}))))))

(defn- arity-binding-arrival
  "One `binary_predicate` membership asserted, read through and retracted, over a
  predicate holding n binary tuples beside one `:default` ternary tuple.

  The membership binds the predicate to two arguments: the settle's refresh reads the
  predicate's shape roster and the tuples of the ternary shape alone, and holds that tuple
  inert (`arity/drain!`, docs/nmtms.md, \"The nogood families\"), so neither the arrival,
  its settle nor the first read at the tuple's context reads a binary tuple."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pArrBind (symbol (str "PAB" i)) 'PABHub) 'CxPerf {})))
    (let [long-tuple (v/assert kb '(pArrBind PABx PABy PABz) 'CxPerf {})]
      (doall (for [_ (range retract-victims)]
               (nanos (let [m (v/assert kb '(binary_predicate pArrBind) 'CxPerf {:strength :monotonic})]
                        (v/believed? kb long-tuple 'CxPerf)
                        (v/retract! kb m))))))))

(defn- metatype-edge-arrival
  "A `:monotonic` `genl` edge from a metatype to `binary_predicate` asserted, read through
  and retracted, over n predicates each holding a `:monotonic` membership of the metatype
  and a binary tuple, one of them also a `:default` ternary tuple; timed per hundred
  predicates.

  The edge binds each member to two arguments, so the arrival stores each member's
  `(binary_predicate P)` (`chain/sync-arity-classes!`) and the settle's refresh holds the
  ternary tuple inert; the retraction withdraws them again.  The cost per member is flat in
  n, so a walk of anything beyond the metatype's members reads as growth."
  [n]
  (let [kb (fresh-kb)
        p  (fn [i] (symbol (str "pMetaEdge" i)))]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pmetaedgekind (p i)) 'CxPerf {:strength :monotonic})
        (v/assert kb (list (p i) (symbol (str "PME" i)) 'PMEHub) 'CxPerf {})))
    (let [long-tuple (v/assert kb (list (p 0) 'PMEx 'PMEy 'PMEz) 'CxPerf {})]
      (doall (for [_ (range 4)]
               (/ (nanos (let [e (v/assert kb '(genl pmetaedgekind binary_predicate) 'CxPerf
                                           {:strength :monotonic})]
                           (v/believed? kb long-tuple 'CxPerf)
                           (v/retract! kb e)))
                  (/ n 100.0)))))))

(defn- arity-binding-under-deep-chain
  "One `(arity pAdc0 3)` asserted and retracted at the bottom of a chain of 64 predicates,
  every eighth bound to two arguments, beside n other predicates each bound to two.

  The binding reads the lengths stored above its predicate from its parents' answers,
  which the arity length entries hold and which probe the bound predicates once per type
  they read (`arity/lengths-of`), and the pairs it forms off the chain alone, so it reads
  none of the n other bindings."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        ch (fn [i] (symbol (str "pAdc" i)))]
    (v/with-deferred-settle kb
      (dotimes [i 63] (v/assert kb (list 'genl (ch i) (ch (inc i))) 'CxPerf M))
      (doseq [i (range 8 64 8)] (v/assert kb (list 'arity (ch i) 2) 'CxPerf M))
      (dotimes [i n] (v/assert kb (list 'arity (symbol (str "pAdcU" i)) 2) 'CxPerf M)))
    (doall (for [_ (range retract-victims)]
             (nanos (v/retract! kb (v/assert kb (list 'arity (ch 0) 3) 'CxPerf M)))))))

(defn- arity-rebuild-beside-bindings
  "The candidate index rebuilt as `recover` rebuilds it and read once
  (`decide/rebuild-candidates!`, `decide/synced`), over 4,096 facts and n predicates each
  bound to two arguments, with no tuple and no `genl` parent.

  The rebuild owes the arity shapes whole, which the settle's first refresh computes for
  the functors of stored facts (`arity/drain!`), so the rebuild and the read read none of
  the n bindings."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (dotimes [i 4096] (v/assert kb (list 'pArbBody (symbol (str "ARb" i)) 'ARbHub) 'CxPerf {}))
      (dotimes [i n] (v/assert kb (list 'binary_predicate (symbol (str "pArb" i))) 'CxPerf M)))
    (doall (for [_ (range 5)]
             (nanos (do (decide/rebuild-candidates! kb) (decide/synced kb)))))))

(defn- genl-chain-child-first-in-one-batch
  "A chain of n `genl` edges asserted child first in one `with-deferred-settle` batch,
  the closing settle included, per edge, three readings on a KB each.

  Each edge lifts its lower end above its new upper end and breaks the edge under it, so
  the batch leaves the relation without a depth potential (`tax/local-lift`).  The settle
  repairs it (`tax/restore-depths`) before its passes read `genl?`, which walks a
  relation without one unpruned.  No rule reads a negated antecedent, so no edge reads
  its lower end's spec closure (`special/negative-subsumption-seeds`)."
  [n]
  (doall (for [_ (range 3)]
           (let [kb (fresh-kb)
                 M  {:strength :monotonic}
                 ch #(symbol (str "pGcf" %))]
             (quot (nanos (v/with-deferred-settle kb
                            (dotimes [i (dec n)]
                              (v/assert kb (list 'genl (ch i) (ch (inc i))) 'CxPerf M))))
                   n)))))

(defn- withheld-mint-beside-covers
  "One fact whose argument type mints a membership that the term's stored, more specific
  membership withholds (`checks/subsumed-mint`), beside n covers of the minted type, per
  fact, 200 readings.

  A withheld mint stores nothing, so `special/entail-arg-type` decides the withholding
  before the admission checks.  The checks' cover arm asks the provers once per cover
  over the type (`checks/cover-refutations`)."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        xs (mapv #(symbol (str "WmcX" %)) (range 200))]
    (v/with-deferred-settle kb
      (v/assert kb '(genl wmc_kind thing) 'CxPerf M)
      (v/assert kb '(genl wmc_sub wmc_kind) 'CxPerf M)
      (v/assert kb '(arg wmcRel 1 wmc_kind) 'CxPerf M)
      (dotimes [i n]
        (v/assert kb (list 'covering 'wmc_kind (symbol (str "wmc_a" i)) (symbol (str "wmc_b" i)))
                  'CxPerf M))
      (doseq [x xs] (v/assert kb (list 'wmc_sub x) 'CxPerf {})))
    (doall (for [x xs] (nanos (v/assert kb (list 'wmcRel x 'WmcY) 'CxPerf {}))))))

(defn- arity-refresh-under-bound-chain
  "A chain of n predicates, each bound to two arguments in CxUniverse, then the arity
  shapes owed whole as `recover` owes them and settled (`decide/rebuild-candidates!`,
  `arity/drain!`), read per hundred predicates.

  The whole refresh syncs the pairs of every bound predicate (`arity/pair-sets`), and a
  predicate with one length at or above it reads no closure (`arity/lengths-of`).  A walk
  of each predicate's ancestors costs its depth in the chain, so the reading grows with
  n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        ch (fn [i] (symbol (str "pArc" i)))]
    (v/with-deferred-settle kb
      (dotimes [i (dec n)] (v/assert kb (list 'genl (ch i) (ch (inc i))) 'CxPerf M))
      (dotimes [i n] (v/assert kb (list 'arity (ch i) 2) 'CxUniverse M)))
    (doall (for [_ (range 3)]
             (quot (nanos (do (decide/rebuild-candidates! kb) (settle/settle kb))) (quot n 100))))))

(defn- arity-pairs-below-a-queued-binding
  "A chain of n predicates, each bound to two arguments in CxUniverse but the bottom one,
  bound to three, with the arity length entries pinned to a weight of 64
  (`set-cache-limit`); then a binding of the top predicate stored and retracted, the
  store timed through its settle and read per hundred predicates.

  The settle syncs the pairs at the top predicate and below it (`arity/pair-sets` under
  `:both`), which asks each predicate below it for the lengths stored at or below it
  (`arity/below-lengths`).  The sync holds each answer for its pass, so each is built
  once.  An answer the bounded entries evict before it is read is built again from the
  chain below it, and reads here as growth with n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        ch (fn [i] (symbol (str "pApb" i)))]
    (v/with-deferred-settle kb
      (dotimes [i (dec n)] (v/assert kb (list 'genl (ch i) (ch (inc i))) 'CxPerf M))
      (dotimes [i n] (v/assert kb (list 'arity (ch i) (if (zero? i) 3 2)) 'CxUniverse M)))
    (settle/settle kb)
    (v/set-cache-limit :arity-lengths 64)
    (try
      (doall (for [_ (range 5)]
               (let [h (atom nil)
                     t (nanos (reset! h (v/assert kb (list 'arity (ch (dec n)) 2) 'CxPerf M)))]
                 (v/retract! kb @h)
                 (quot t (quot n 100)))))
      (finally (v/set-cache-limit :arity-lengths nil)))))

(defn- bound-type-load
  "n types in eight levels under one root, each below three types of the level above,
  then every type bound to one argument, the bottom level first, each binding timed.

  A length arriving at a type refreshes only the subtypes whose own binding does not give
  it (`arity/moved-below`), and the pairs it forms are read only in the subtypes storing
  another length (docs/nmtms.md, \"The nogood families\").  Bottom level first makes the
  last bindings the top level's, whose subtypes are most of the load and all bound
  already, so the readings are what an arrival costs where nothing below it moves: the
  walk stops at each child.  A recompute of every subtype per binding reads here as
  growth with the load."
  [n]
  (let [kb     (fresh-kb)
        levels 8
        width  (max 1 (quot n levels))
        rnd    (java.util.Random. 57)
        ty     (fn [l i] (symbol (str "btl" l "i" i "_t")))]
    (v/with-deferred-settle kb
      (doseq [l (range levels), i (range width)]
        (if (zero? l)
          (v/assert kb (list 'genl (ty 0 i) 'btroot_t) 'CxPerf {})
          (dotimes [_ 3]
            (v/assert kb (list 'genl (ty l i) (ty (dec l) (.nextInt rnd width))) 'CxPerf {})))))
    (doall
     (for [l (range (dec levels) -1 -1), i (range width)]
       (nanos (v/assert kb (list 'arity (ty l i) 1) 'CxPerf {:strength :monotonic}))))))

(defn- declaration-rebuild
  "n types in a chain under `thing`, one `arg` declaration naming each, then
  `special/rebuild-pending!` timed whole and read per hundred declarations (one is
  under the noise floor).

  The rebuild answers whether a declared type reaches `thing` from one walk down from
  `thing` (`checks/mintable-types`), so a declaration costs a record read and a set
  lookup.  A walk up from each declaration's type costs its position in the chain, and
  reads here as growth with n."
  [n]
  (let [kb (fresh-kb)
        ty (fn [i] (symbol (str "pdr" i "_t")))]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (ty i) (if (zero? i) 'thing (ty (dec i)))) 'CxPerf
                  {:strength :monotonic})
        (v/assert kb (list 'arg (symbol (str "pdrRel" i)) 1 (ty i)) 'CxPerf
                  {:strength :monotonic})))
    (doall (for [_ (range 4)]
             (/ (nanos (special/rebuild-pending! kb)) (/ n 100.0))))))

(defn- mint-release-after-genl-move
  "n types in a chain with no path to `thing`, one `arg` declaration naming each, so n
  declarations wait on a mintable type; then a `genl` edge between two other types, timed
  through the settle that re-asks every waiting declaration, read per hundred
  declarations.

  The settle answers each declaration from one walk down from `thing`
  (`checks/mintable-types`).  A walk up from each declaration's type costs its position
  in the chain, and reads here as growth with n."
  [n]
  (let [kb (fresh-kb)
        ty (fn [i] (symbol (str "pmr" i "_t")))]
    (v/with-deferred-settle kb
      ;; `thing` a node, so a walk up from the chain is not refused on depth alone
      (v/assert kb '(genl pmr_anchor_t thing) 'CxPerf {:strength :monotonic})
      (doseq [i (range n)]
        (when (pos? i)
          (v/assert kb (list 'genl (ty i) (ty (dec i))) 'CxPerf {:strength :monotonic}))
        (v/assert kb (list 'arg (symbol (str "pmrRel" i)) 1 (ty i)) 'CxPerf
                  {:strength :monotonic})))
    (doall (for [k (range 4)]
             (/ (nanos (v/assert kb (list 'genl (symbol (str "pmr_sub" k "_t"))
                                          (symbol (str "pmr_top" k "_t")))
                                 'CxPerf {:strength :monotonic}))
                (/ n 100.0))))))

(defn- arg-declaration-over-facts
  "n facts of `pdoRel`, whose first argument a declaration types with the bottom of a
  chain of n types that has no path to `thing`; then four `arg` declarations of its
  second argument, each naming a type under `thing`, timed with their settles and read
  per hundred facts.  Each declaration mints one membership per fact.

  A declaration's sweep reads only its own declaration
  (`checks/declaration-entailments`), so the chain's type is not asked whether it
  reaches `thing`.  Asking it once per fact costs a walk of the chain per fact, and
  reads here as growth with n."
  [n]
  (let [kb    (fresh-kb)
        m     {:strength :monotonic}
        down  (fn [i] (symbol (str "pdo_down" i "_t")))
        added (fn [k] (symbol (str "pdo_new" k "_t")))]
    (v/with-deferred-settle kb
      (doseq [i (range 1 n)]
        (v/assert kb (list 'genl (down i) (down (dec i))) 'CxPerf m))
      (dotimes [k 4]
        (v/assert kb (list 'genl (added k) 'thing) 'CxPerf m))
      (v/assert kb (list 'arg 'pdoRel 1 (down (dec n))) 'CxPerf m))
    (v/bulk-assert-facts! kb (for [i (range n)]
                               (list 'pdoRel (symbol (str "PdoA" i)) (symbol (str "PdoB" i))))
                          'CxPerf)
    (doall (for [k (range 4)]
             (/ (nanos (v/assert kb (list 'arg 'pdoRel 2 (added k)) 'CxPerf m))
                (/ n 100.0))))))

(defn- membership-under-deep-type
  "A chain of n types under `thing`, one `arg` declaration and one forward rule over
  types outside the chain, then 200 memberships in the chain's bottom type, timed one
  apiece.

  A membership's own functor is asked for the declarations above it
  (`res/constraining-predicates`) and for the rules its arrival triggers
  (`rules/trigger-keys`), and each intersects the type's up-closure with a roster by
  walking the smaller of the two.  Walking the closure costs the type's depth per
  membership, and reads here as growth with n."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}
        ty (fn [i] (symbol (str "pmd" i "_t")))]
    (v/with-deferred-settle kb
      (v/assert kb '(genl pmd_other_t thing) 'CxPerf m)
      (v/assert kb '(arg pmdRel 1 pmd_other_t) 'CxPerf m)
      (v/assert kb '(implies (and (pmd_other_t ?x)) (pmd_tagged_t ?x)) 'CxPerf m)
      (doseq [i (range n)]
        (v/assert kb (list 'genl (ty i) (if (zero? i) 'thing (ty (dec i)))) 'CxPerf m)))
    (let [leaf (ty (dec n))]
      (doall (for [i (range 200)]
               (nanos (v/assert kb (list leaf (symbol (str "Pmd" i))) 'CxPerf)))))))

(def ^:private lift-rebuild-facts
  "The facts of a decontextualized predicate `lift-rebuild` states in its deepest context."
  2000)

(defn- lift-rebuild
  "A chain of n contexts under CxPerf, an `except` of the chain's first `genlCx` edge from
  a side context (so a scoped `sees?` reads each edge supporter's visibility), and
  `lift-rebuild-facts` facts of a decontextualized predicate stated in the deepest
  context; then `special/rebuild-pending!` timed whole and read per hundred facts.

  The lift walk asks whether a stating context sees CxUniverse once per context
  (`special/lift-statements`).  Asking it per fact walks the chain per fact, and reads
  here as growth with n."
  [n]
  (let [kb (fresh-kb)
        cx (fn [i] (symbol (str "CxPlr" i)))]
    (v/with-deferred-settle kb
      (v/assert kb '(genlCx CxPerf CxUniverse) 'CxUniverse {:strength :monotonic})
      (v/assert kb '(genlCx CxPlrSide CxPerf) 'CxUniverse {:strength :monotonic})
      (v/assert kb '(decontextualized_predicate pLiftRebuild) 'CxUniverse {:strength :monotonic})
      (doseq [i (range 1 (inc n))]
        (let [h (v/assert kb (list 'genlCx (cx i) (if (= 1 i) 'CxPerf (cx (dec i))))
                          'CxUniverse {:strength :monotonic})]
          (when (= 1 i)
            (v/assert kb (list 'except (list 'sentexHandle h)) 'CxPlrSide
                      {:strength :monotonic}))))
      (doseq [j (range lift-rebuild-facts)]
        (v/assert kb (list 'pLiftRebuild (symbol (str "PLR" j)) 'PLRHub) (cx n) {})))
    (doall (for [_ (range 4)]
             (/ (nanos (special/rebuild-pending! kb)) (/ lift-rebuild-facts 100.0))))))

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
  walks the same subtree at `special/equate-under-edge` under the mark, so an edge
  written once measures both passes and can separate neither; a
  revival puts the edge back in the moved region without going through that path, and the
  reading is the settle's two budgeted walks: the constraint pass and the merge sweep a
  revived edge under a mark runs (`special/revived-edge-sweep`).  The mark is declared either way, so the report's
  vocabulary gate is open in both shapes and the only difference is the one being measured.
  The predicates are spelled bare lowercase, which `checks/forced-monotonic?` takes as a
  type spelling, so the edge is not a `genl` between predicates, which the forced-monotonic
  roster holds and no denial defeats (docs/nmtms.md)."
  [marked? budget]
  (fn [n]
    (binding [tax/*exposure-instance-budget* budget]
      (let [kb (fresh-kb)]
        (v/assert kb (list 'functional (if marked? 'pcegtop 'pcegelse))
                  'CxPerf {:strength :monotonic})
        (v/with-deferred-settle kb
          (v/assert kb '(genl pcegmid pcegtop) 'CxPerf {})
          (v/assert kb '(genl pcegsub pcegmid) 'CxPerf {})
          (doseq [i (range n)]
            (v/assert kb (list 'pcegsub (symbol (str "PCEG" i)) 'PCEGval) 'CxPerf {})))
        (let [edge '(not (genl pcegmid pcegtop))]
          (doall
           (for [_ (range edge-writes)]
             (nanos (let [h (v/assert kb edge 'CxPerf {:strength :monotonic})]
                      (v/retract! kb h))))))))))

(def ^:private reads-per-visibility-reading
  "Reads batched into one timed measurement, the same batch at both sizes so it cancels
  out of the ratio — `reads-per-clash-reading`'s idiom, for its reason."
  20)

(defn- visibility-reading
  "A scoped read on a KB carrying n believed `(except (sentexHandle H))` facts, all
  visible from the reading context.

  The claim is that the read costs **what it returns**, not what the KB hides. Every
  scoped retrieval filters by visibility removal (`exc/without-excepted`), and the answer
  that filter needs is *which handles are hidden from here* — a question whose intended
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

(def ^:private hidden-arg-contexts
  "Contexts the decoys of `scoped-arg-read` are spread over, the same count at both sizes,
  so n moves how many facts each holds and not how many contexts there are."
  16)

(defn- scoped-arg-read
  "A context-scoped read `(psaLikes PSATom ?x)` from `CxPerf`, on a KB holding n more
  `psaLikes` facts about `PSATom` stated in contexts `CxPerf` does not see.

  The answer is one fact at every n.  The bound argument's argument-root node lists the
  contexts that state such a fact, so a read that intersects them with the reader's
  ancestor set reads the one leaf it sees.  A read that takes every candidate under the
  node and drops the invisible ones after fetching each record grows with n, and so does
  a trie walk that fans over every stored `?x` before it reaches the context level.
  Each reading takes both retrievals: `sentexes-matching` (the level-2 matcher, the
  pattern's own context) and `res/matches-visible` (the hierarchical read, the context's
  ancestor set).

  The literal cache is bound off, as in `visibility-reading` and for its reason."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'psaLikes 'PSATom (symbol (str "PSAX" i)))
                  (symbol (str "CxPsaHidden" (mod i hidden-arg-contexts)))
                  {:strength :monotonic})))
    (v/assert kb '(psaLikes PSATom PSAOne) 'CxPerf {:strength :monotonic})
    (binding [lc/*enabled* false]
      (doall
       (for [_ (range 60)]
         (nanos (dotimes [_ reads-per-visibility-reading]
                  (count (v/sentexes-matching kb '(psaLikes PSATom ?x) 'CxPerf))
                  (count (res/matches-visible kb '(psaLikes PSATom ?x) 'CxPerf)))))))))

(defn- scoped-trie-prefix-read
  "A context-scoped read `(ptpScore PTPTeam PTPYear ?v)` from `CxPerf` through
  `res/matches-visible`, on a KB holding n more `ptpScore` facts under the same two
  leading arguments stated in contexts `CxPerf` does not see: sixteen values of `?v`,
  each stated in n/16 contexts.

  The answer is one fact at every n.  Two ground arguments followed by a variable take
  the trie walk under that prefix (`:hier-trie-prefix`), which fans over the seventeen
  stored values of `?v` and then reaches the context level.  A walk that keeps that level
  to the reader's ancestor set probes each value's contexts against the set and reads the
  leaves it sees.  A walk that fans the level over every child grows with n: each
  invisible leaf's handles are fetched before the context filter drops them.  The values
  are held at sixteen because the walk's fan over the stored values grows with their
  number whatever the reader sees.  The literal cache is bound off, as in
  `scoped-arg-read`."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'ptpScore 'PTPTeam 'PTPYear (symbol (str "PTPV" (mod i 16))))
                  (symbol (str "CxPtpHidden" (quot i 16)))
                  {:strength :monotonic})))
    (v/assert kb '(ptpScore PTPTeam PTPYear PTPOne) 'CxPerf {:strength :monotonic})
    (binding [lc/*enabled* false]
      (doall
       (for [_ (range 60)]
         (nanos (dotimes [_ reads-per-visibility-reading]
                  (count (res/matches-visible kb '(ptpScore PTPTeam PTPYear ?v) 'CxPerf)))))))))

(defn- scoped-trie-prefix-fan-read
  "`scoped-trie-prefix-read` with the n matches `CxPerf` does not see holding n distinct
  values of `?v`, spread over sixteen contexts.  A trie walk under the prefix visits every
  value before it reaches the context level, so it grows with n; the argument roots read
  against `CxPerf`'s ancestor set read the one leaf it sees."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'ptfScore 'PTFTeam 'PTFYear (symbol (str "PTFV" i)))
                  (symbol (str "CxPtfHidden" (mod i hidden-arg-contexts)))
                  {:strength :monotonic})))
    (v/assert kb '(ptfScore PTFTeam PTFYear PTFOne) 'CxPerf {:strength :monotonic})
    (binding [lc/*enabled* false]
      (doall
       (for [_ (range 60)]
         (nanos (dotimes [_ reads-per-visibility-reading]
                  (count (res/matches-visible kb '(ptfScore PTFTeam PTFYear ?v) 'CxPerf)))))))))

(defn- variable-context-prefix-read
  "A read `(pvcScore PVCTeam PVCYear ?v)` at a variable context through
  `res/matches-visible`, with 64 matches stated in `CxPerf`, beside n facts
  `(pvcScore PVCTeam PVCOtherI PVCVI)` that `PVCYear` rules out, four to a context.

  The answer is the 64 matches at every n.  `PVCYear` holds 64 facts in one context, so
  the argument roots lead and `PVCYear` leads the intersection: one context, probed
  against `PVCTeam`'s, and one leaf intersection there.  An intersection led by
  `PVCTeam` fans over its n/4 contexts and grows with n.  The literal cache is bound off,
  as in `scoped-arg-read`."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pvcScore 'PVCTeam (symbol (str "PVCOther" i)) (symbol (str "PVCV" i)))
                  (symbol (str "CxPvcHidden" (quot i 4)))
                  {:strength :monotonic}))
      (doseq [i (range 64)]
        (v/assert kb (list 'pvcScore 'PVCTeam 'PVCYear (symbol (str "PVCMatch" i))) 'CxPerf
                  {:strength :monotonic})))
    (binding [lc/*enabled* false]
      (doall
       (for [_ (range 60)]
         (nanos (dotimes [_ reads-per-visibility-reading]
                  (count (res/matches-visible kb '(pvcScore PVCTeam PVCYear ?v) '?ctx)))))))))

(defn- scoped-defeat-read
  "Whether a defeat is stated in a context `CxPerf` sees, asked from a fresh read state at
  `CxPerf`, on a KB holding n placed defeats stated in contexts `CxPerf` does not see.

  Each hidden context holds n/16 denied defaults, `(pdr_t PDRi)` and its monotonic
  denial, and the nogood places a `defeat` of the default there.  The answer is false at
  every n.  The predicate extent of `defeat` lists the contexts that state one, so the
  question intersects them with the reader's ancestor set; a scan of every stored defeat
  by target grows with n.  The private read state is the one `exc/believed-in` takes,
  and a belief read asks the question before it walks a handle's support."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [s (list 'pdr_t (symbol (str "PDR" i)))
                    c (symbol (str "CxPdrHidden" (mod i hidden-arg-contexts)))]]
        (v/assert kb s c {})
        (v/assert kb (list 'not s) c M)))
    (v/assert kb '(pdr_t PDROne) 'CxPerf {})
    (let [state #(#'exc/reader-state kb 'CxPerf)]
      (when (#'exc/sees-defeat? (state))
        (throw (ex-info "CxPerf sees a defeat stated where it cannot see" {})))
      (doall
       (for [_ (range 60)]
         (nanos (dotimes [_ reads-per-visibility-reading] (#'exc/sees-defeat? (state)))))))))

(defn- scoped-genl-census
  "Scoped `genls` and `genl?` reads at `CxPerf`, on a KB holding n `genl` edges each
  stated in its own context, none of which `CxPerf` sees.

  The answer is the same at every n.  A scoped read intersects `CxPerf`'s ancestor set
  with the contexts the `genl` extent lists, iterating the smaller side
  (`tax/visible-ctxs`), so it costs what `CxPerf` sees; an intersection that walks every
  context stating an edge grows with n."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "pgc_s" i)) 'pgc_top)
                  (symbol (str "CxPgcHidden" i)) {})))
    (v/assert kb '(genl pgc_a pgc_top) 'CxPerf {})
    (doall
     (for [_ (range 60)]
       (nanos (dotimes [_ reads-per-visibility-reading]
                (v/genls kb 'pgc_a 'CxPerf)
                (v/genl? kb 'pgc_a 'pgc_top 'CxPerf)))))))

(defn- scoped-rule-read
  "The backward candidate rules for a goal on `prrQ` and for a goal whose functor is
  open, asked from `CxPerf`, on a KB holding n more rules on antecedent `prr_p` concluding
  `prrQ` stated in contexts `CxPerf` does not see.

  The answer is one rule at every n.  The open functor's candidates are the rules on each
  antecedent key, read from the antecedent index; the bound one's are the rules on its
  consequent.  Both indexes end in the context, so a read given the reader's ancestor set
  reads the one rule it sees; a read that fetches every rule's record and drops the
  invisible ones grows with n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        rule (fn [x] (rules/rule-sentence ['(prr_p ?x)] (list 'prrQ '?x x)))]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (rule (symbol (str "PRR" i)))
                  (symbol (str "CxPrrHidden" (mod i hidden-arg-contexts))) M)))
    (v/assert kb (rule 'PRROne) 'CxPerf M)
    (doall
     (for [_ (range 60)]
       (nanos (dotimes [_ reads-per-visibility-reading]
                (count (provers/candidate-rules kb '(prrQ PRRA ?y) 'CxPerf))
                (count (provers/candidate-rules kb '(?p PRRA ?y) 'CxPerf))))))))

(def ^:private readings-per-reader-fan
  "Timed readings.  Above `tail-samples`, so the answer is a mean over the last 50 and the
  first reading — the only one that still has merges to derive — is outside it."
  60)

(defn- genlcx-edge-under-a-seen-taxonomy
  "One `(genlCx sub other)` edge whose `sub` already sees a context stating n `genl`
  edges, and whose `other` is new and holds one fact a rule reads.  The rule reads a type
  outside the n-edge tree, so the edge newly connects one fact to one rule at both n.

  The claim is that `special/visibility-seeds` costs what the edge newly connects.  The
  edges `sub` already sees are `seen`'s, and the seeding owed to them reads the cheaper
  of `seen`'s edges and `up`'s rule-relevant postings (`special/under-seen-edges`), which
  here is `other`'s one fact.  A reading that grows with n is the seeding walking every
  edge `sub` sees.  Each reading wires a fresh `sub` and `other`, untimed."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genl gstroot thing) 'CxGstTax m)
    (v/bulk-assert-facts! kb (for [i (range 1 n)]
                               (list 'genl (symbol (str "gstty" i))
                                     (if (< i 10) 'gstroot (symbol (str "gstty" (quot i 10))))))
                          'CxGstTax)
    (v/assert kb '(genl gstleaf thing) 'CxGstTax m)
    (v/assert kb '(implies (gstleaf ?x) (gstmarked ?x)) 'CxGstTax)
    (doall
     (for [i (range 60)
           :let [sub   (symbol (str "CxGstSub" i))
                 other (symbol (str "CxGstOther" i))]]
       (do (v/assert kb (list 'genlCx sub 'CxGstTax) 'CxUniverse m)
           (v/assert kb (list 'gstleaf (symbol (str "GstInd" i))) other {})
           (nanos (v/assert kb (list 'genlCx sub other) 'CxUniverse m)))))))

(defn- genlcx-edge-beside-declared-facts
  "One `(genlCx sub CxGdaTheory)` edge over a `sub` holding one fact of a predicate an
  argument declaration in `CxGdaTheory` types, beside n facts of that predicate stored in
  another context under it.

  The claim is that `special/entail-under-context-edge` costs the smaller of the edge's
  extent and the declared extent: here the edge brings one fact under the declaration at
  both n, and a reading that grows with n is the arm walking every fact of the declared
  predicate.  Each reading wires a fresh `sub`, untimed but for the edge."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genlCx CxGdaTheory CxUniverse) 'CxUniverse m)
    (v/assert kb '(genlCx CxGdaBulk CxGdaTheory) 'CxUniverse m)
    (v/assert kb '(genl gda_kind thing) 'CxGdaTheory m)
    (v/assert kb '(arg gdaHolds 2 gda_kind) 'CxGdaTheory m)
    (v/bulk-assert-facts! kb (for [i (range n)]
                               (list 'gdaHolds (symbol (str "GdaA" i)) (symbol (str "GdaB" i))))
                          'CxGdaBulk)
    (doall
     (for [i (range 60)
           :let [sub (symbol (str "CxGdaSub" i))]]
       (do (v/assert kb (list 'gdaHolds (symbol (str "GdaS" i)) (symbol (str "GdaT" i))) sub)
           (nanos (v/assert kb (list 'genlCx sub 'CxGdaTheory) 'CxUniverse m)))))))

(defn- genlcx-edge-beside-seen-declared-facts
  "One `(genlCx sub CxGsdY)` edge, where `sub` sits under `CxGsdR`, which states an `arg`
  declaration and sits under `CxGsdTop`, beside n facts of the declared predicate stated
  in `CxGsdTop`.  `sub` saw `CxGsdTop` before the edge, so the edge gives no fact there a
  placement it did not have.

  The claim is that `special/entail-under-context-edge` draws a declaration a context
  under `sub` sees over the facts stated where the edge newly shows `sub`, and not over
  every fact `super` sees.  Each reading wires a fresh `sub`, untimed but for the edge."
  [n]
  (binding [checks/*assertive-arg-types?* true]
    (let [kb (fresh-kb)
          m  {:strength :monotonic}]
      (doseq [[s g] '[[CxGsdTop CxUniverse] [CxGsdR CxGsdTop] [CxGsdY CxGsdTop]]]
        (v/assert kb (list 'genlCx s g) 'CxUniverse m))
      (v/assert kb '(genl gsd_kind thing) 'CxUniverse m)
      (v/assert kb '(arg gsdRel 1 gsd_kind) 'CxGsdR m)
      (v/bulk-assert-facts! kb (for [i (range n)]
                                 (list 'gsdRel (symbol (str "GsdA" i)) 'GsdThing))
                            'CxGsdTop)
      (doall
       (for [i (range 60)
             :let [sub (symbol (str "CxGsdX" i))]]
         (do (v/assert kb (list 'genlCx sub 'CxGsdR) 'CxUniverse m)
             (nanos (v/assert kb (list 'genlCx sub 'CxGsdY) 'CxUniverse m))))))))

(defn- genlcx-edge-showing-an-empty-context
  "One `(genlCx CxGecR sub)` edge to a fresh `sub` that stores nothing and sees no context,
  where `CxGecR` sees `CxGecTop`, which states an `arg` declaration and n facts of the
  declared predicate.

  The claim is that `special/entail-under-context-edge` reads no fact when the contexts
  the edge newly shows `CxGecR` store nothing.  The n facts are in the move's `:below`,
  since `sub` sees none of them, so a reading that grows with n is the arm drawing each
  of them again.  Each reading asserts the edge to a fresh `sub`."
  [n]
  (binding [checks/*assertive-arg-types?* true]
    (let [kb (fresh-kb)
          m  {:strength :monotonic}]
      (doseq [[s g] '[[CxGecTop CxUniverse] [CxGecR CxGecTop]]]
        (v/assert kb (list 'genlCx s g) 'CxUniverse m))
      (v/assert kb '(genl gec_kind thing) 'CxUniverse m)
      (v/assert kb '(arg gecRel 1 gec_kind) 'CxGecTop m)
      (v/bulk-assert-facts! kb (for [i (range n)]
                                 (list 'gecRel (symbol (str "GecA" i)) 'GecThing))
                            'CxGecTop)
      (doall
       (for [i (range 60)]
         (nanos (v/assert kb (list 'genlCx 'CxGecR (symbol (str "CxGecS" i))) 'CxUniverse m)))))))

(defn- fact-beside-distant-declarations
  "A fact asserted into `CxFdF`, which sits under `CxFdTop` and has one child, beside n
  `arg` declarations of its predicate, each in its own context under `CxFdTop` that shares
  no descendant with `CxFdF`.

  The claim is that `special/declarations-below` reads the declarations stated where a
  descendant of the fact's context sees them, and not every declaration of the predicate.
  Each reading asserts a fresh fact."
  [n]
  (binding [checks/*assertive-arg-types?* true]
    (let [kb (fresh-kb)
          m  {:strength :monotonic}]
      (doseq [[s g] '[[CxFdTop CxUniverse] [CxFdF CxFdTop] [CxFdLeaf CxFdF]]]
        (v/assert kb (list 'genlCx s g) 'CxUniverse m))
      (v/with-deferred-settle kb
        (doseq [i (range n)
                :let [c (symbol (str "CxFdSide" i))
                      t (symbol (str "fd_kind" i))]]
          (v/assert kb (list 'genlCx c 'CxFdTop) 'CxUniverse m)
          (v/assert kb (list 'genl t 'thing) 'CxUniverse m)
          (v/assert kb (list 'arg 'fdRel 1 t) c m)))
      (doall
       (for [i (range 60)]
         (nanos (v/assert kb (list 'fdRel (symbol (str "FdA" i)) 'FdThing) 'CxFdF m)))))))

(defn- genlcx-edge-leaving-beside-distant-mints
  "One `(genlCx sub CxGlJ)` edge retracted, where `sub` and `CxGlJ` each sit under `CxGlL`
  and `CxGlR` and `CxGlJ` holds the mint of a fact in `CxGlL` and a declaration in
  `CxGlR`, beside n mints stated in a context the edge does not reach.

  The claim is that `special/departed-context-edge-mints` reads the mints placed in the
  contexts `sub` no longer sees, one here at both n, and not every stored mint.  Each
  reading wires a fresh `sub` and asserts the edge, untimed, and times the retraction."
  [n]
  (binding [checks/*assertive-arg-types?* true]
    (let [kb (fresh-kb)
          m  {:strength :monotonic}]
      (doseq [[s g] '[[CxGlL CxUniverse] [CxGlR CxUniverse] [CxGlFar CxUniverse]
                      [CxGlJ CxGlL] [CxGlJ CxGlR]]]
        (v/assert kb (list 'genlCx s g) 'CxUniverse m))
      (v/assert kb '(genl gl_kind thing) 'CxUniverse m)
      (v/assert kb '(arg glRel 1 gl_kind) 'CxGlR m)
      (v/assert kb '(glRel GlA GlB) 'CxGlL m)
      (v/assert kb '(arg glOwns 1 gl_kind) 'CxGlFar m)
      (v/with-deferred-settle kb
        (doseq [i (range n)]
          (v/assert kb (list 'glOwns (symbol (str "GlF" i)) 'GlThing) 'CxGlFar m)))
      (doall
       (for [i (range 60)
             :let [sub  (symbol (str "CxGlK" i))
                   edge (list 'genlCx sub 'CxGlJ)]]
         (do (v/assert kb (list 'genlCx sub 'CxGlL) 'CxUniverse m)
             (v/assert kb (list 'genlCx sub 'CxGlR) 'CxUniverse m)
             (v/assert kb edge 'CxUniverse m)
             (nanos (v/retract! kb (v/handle-of kb edge 'CxUniverse)))))))))

(defn- genlcx-edge-beside-excepted-declarations
  "One `(genlCx sub CxGedOther)` edge beside n `arg` declarations, each over 16 facts and
  each excepted in `CxGedHide`, a context `CxGedOther` does not see.  Each fact's second
  argument is already a `ged_sub`, so the declaration's `ged_kind` is withheld as a
  subsumed mint and the declaration supports nothing.

  The claim is that a `genlCx` edge costs what it reaches.  It re-checks the `except`s
  stated in a context the edge's `super` sees (`special/recheck-except-ancestors`), and
  reads no declared functor over a `sub` storing nothing.  Here the edge moves no `except`
  at both n, and a reading that grows with n is the edge re-asking every `except` or
  drawing again over each excepted declaration's extent.  Each reading wires a fresh
  `sub`, untimed but for the edge."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genlCx CxGedHide CxUniverse) 'CxUniverse m)
    (v/assert kb '(genlCx CxGedOther CxUniverse) 'CxUniverse m)
    (v/assert kb '(genl ged_kind thing) 'CxUniverse m)
    (v/assert kb '(genl ged_sub ged_kind) 'CxUniverse m)
    (doseq [k (range n)
            :let [rel (symbol (str "gedRel" k))]]
      (let [dh (v/assert kb (list 'arg rel 2 'ged_kind) 'CxUniverse m)]
        (doseq [i (range 16)
                :let [b (symbol (str "GedB" k "x" i))]]
          (v/assert kb (list 'ged_sub b) 'CxUniverse)
          (v/assert kb (list rel (symbol (str "GedA" k "x" i)) b) 'CxUniverse))
        (v/assert kb (list 'except (list 'sentexHandle dh)) 'CxGedHide m)))
    (doall
     (for [i (range 60)
           :let [sub (symbol (str "CxGedSub" i))]]
       (nanos (v/assert kb (list 'genlCx sub 'CxGedOther) 'CxUniverse m))))))

(defn- trigger-membership-beside-declared-facts
  "One `(pvt_carnivore x)` membership arriving after a fact `(pvtEats x y)` that an
  `(interArg pvtEats 1 pvt_carnivore 2 pvt_meat)` declaration reads it as the trigger of,
  beside n facts of `pvtEats` that do not name `x`.

  The claim is that `special/triggered-mints` reads the smaller of the term's postings
  and the declared extent: here the membership's term names one declared fact at both n,
  and a reading that grows with n is the arm walking every fact of the declared
  predicate.  Each reading stores a fresh fact, untimed, then times its trigger."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genl pvt_carnivore thing) 'CxUniverse m)
    (v/assert kb '(genl pvt_meat thing) 'CxUniverse m)
    (v/assert kb '(interArg pvtEats 1 pvt_carnivore 2 pvt_meat) 'CxUniverse m)
    (v/bulk-assert-facts! kb (for [i (range n)]
                               (list 'pvtEats (symbol (str "PvtA" i)) (symbol (str "PvtB" i))))
                          'CxUniverse)
    (doall
     (for [i (range 60)
           :let [x (symbol (str "PvtX" i))]]
       (do (v/assert kb (list 'pvtEats x (symbol (str "PvtY" i))) 'CxUniverse)
           (nanos (v/assert kb (list 'pvt_carnivore x) 'CxUniverse)))))))

(defn- declaration-at-a-leaf-beside-unseen-memberships
  "One `(forced_monotonic_predicate T)` declaration at a fresh leaf context beside n
  memberships of `T` stated in `CxDlFar`, a context the leaf does not see.

  The claim is that a declaration costs the readers that see it (docs/nmtms.md, \"The
  forced-monotonic roster\"): it forces `T` at the leaf alone, so the switch rewrites the
  forced memberships of the rules reading or concluding `T` (`checks/force-reach!`), and
  the placement pass reads the facts of `T` stated where the leaf sees
  (`chain/declared-reach`).  Here both are empty at both n, and a reading that grows with
  n is the switch or the pass reading every fact of `T`.  Each reading declares a fresh
  type over its own n memberships, wired untimed."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genlCx CxDlFar CxUniverse) 'CxUniverse m)
    (doall
     (for [i (range 24)
           :let [t    (symbol (str "dl_kind" i))
                 leaf (symbol (str "CxDlLeaf" i))]]
       (do (v/bulk-assert-facts! kb (for [j (range n)] (list t (symbol (str "DlInd" j)))) 'CxDlFar)
           (v/assert kb (list 'genlCx leaf 'CxUniverse) 'CxUniverse m)
           (nanos (v/assert kb (list 'forced_monotonic_predicate t) leaf)))))))

(defn- declaration-at-a-leaf-beside-a-wide-stating-context
  "One `(forced_monotonic_predicate T)` declaration at a fresh leaf context beside 8
  memberships of `T` stated in `CxWsRoot`, a context with n children that the leaf neither
  sees nor shares a descendant with.

  The claim is that the reach of a declaration (`chain/declaration-reach`) costs the
  smaller of the two down-sets it compares, here the leaf's one context, and not the
  children of a stating context it does not see.  Each reading declares a fresh type over
  its own memberships at a fresh leaf, wired untimed; the leaf retires the closure memo."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genlCx CxWsRoot CxUniverse) 'CxUniverse m)
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxWsKid" i)) 'CxWsRoot) 'CxUniverse m)))
    (doall
     (for [i (range 24)
           :let [t    (symbol (str "ws_kind" i))
                 leaf (symbol (str "CxWsLeaf" i))]]
       (do (v/bulk-assert-facts! kb (for [j (range 8)] (list t (symbol (str "WsInd" j)))) 'CxWsRoot)
           (v/assert kb (list 'genlCx leaf 'CxUniverse) 'CxUniverse m)
           (nanos (v/assert kb (list 'forced_monotonic_predicate t) leaf)))))))

(defn- cxuniverse-declaration-beside-bystander-contexts
  "One `(forced_monotonic_predicate T)` declaration in `CxUniverse` over 32 memberships of `T`
  stated in `CxDcFar` and 8 stated in `CxUniverse`, beside n bystander contexts under
  `CxUniverse` that state nothing of `T`.

  The claim is that a declaration every context sees costs the stored facts of `T`
  (`chain/declaration-reach`), read in one probe of the predicate extent, and not the
  contexts: a reach built from the ancestor sets of the contexts below `CxUniverse` grows
  with n here and with the facts nowhere.  Each reading declares a fresh type over its own
  memberships, wired untimed, and a context added under `CxUniverse` before each one
  retires the closure memo."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(genlCx CxDcFar CxUniverse) 'CxUniverse m)
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxDcBy" i)) 'CxUniverse) 'CxUniverse m)))
    (doall
     (for [i (range 24)
           :let [t (symbol (str "dc_kind" i))]]
       (do (v/bulk-assert-facts! kb (for [j (range 32)] (list t (symbol (str "DcInd" j)))) 'CxDcFar)
           (v/bulk-assert-facts! kb (for [j (range 8)] (list t (symbol (str "DcTop" j)))) 'CxUniverse)
           ;; a new context retires the closure memo, so the declaration reads each
           ;; context set afresh and a walk of the contexts below shows as growth
           (v/assert kb (list 'genlCx (symbol (str "CxDcGen" i)) 'CxUniverse) 'CxUniverse m)
           (nanos (v/assert kb (list 'forced_monotonic_predicate t) 'CxUniverse)))))))

(defn- declaration-beside-stating-contexts-over-a-wide-descendant
  "One `(forced_monotonic_predicate T)` declaration at `CxSwC`, which has n contexts below
  it, beside one membership of `T` stated in each of n contexts `CxSwX…`, all above
  `CxSwY`, which has n contexts below it.  No stating context shares a descendant with
  `CxSwC`.

  The claim is that the reach of a declaration (`chain/declaration-reach`) walks the
  contexts below the declaring context once per call, and not once per stating context:
  the declaration reads the n stating contexts, so it grows with n, and a walk per
  stating context grows with the square of n.  Each reading declares a fresh type over
  its own memberships, wired untimed."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}
        xs (mapv #(symbol (str "CxSwX" %)) (range n))]
    (v/with-deferred-settle kb
      (v/assert kb '(genlCx CxSwC CxUniverse) 'CxUniverse m)
      (v/assert kb '(genlCx CxSwZ CxSwC) 'CxUniverse m)
      (doseq [x xs]
        (v/assert kb (list 'genlCx x 'CxUniverse) 'CxUniverse m)
        (v/assert kb (list 'genlCx 'CxSwY x) 'CxUniverse m))
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxSwZk" i)) 'CxSwZ) 'CxUniverse m)
        (v/assert kb (list 'genlCx (symbol (str "CxSwYk" i)) 'CxSwY) 'CxUniverse m)))
    (doall
     (for [i (range 12)
           :let [t (symbol (str "sw_kind" i))]]
       (do (doseq [x xs] (v/assert kb (list t 'SwInd) x))
           (nanos (v/assert kb (list 'forced_monotonic_predicate t) 'CxSwC)))))))

(defn- membership-clash-beside-denied-cxuniverse-declarations
  "A clashing membership pair under a `disjoint` at a fresh context, beside n
  `(forced_monotonic_predicate T)` declarations in `CxUniverse`, each denied there at
  `:monotonic`, so a placed defeat in force at every reader names each declaration.

  The claim is that a reader's roster reading (`except/roster-state`) runs the `in-force?`
  of a defeat naming a declaration only for a predicate a stored denial or a rule reads,
  and none of the n does: a write that reads visibility asks the reader's roster once
  per handle it checks, so a reading that weighs every declaration grows with n.  Each
  reading clashes a fresh pair at a fresh context, wired untimed."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (doseq [i (range n)
            :let [decl (list 'forced_monotonic_predicate (symbol (str "dd_kind" i)))]]
      (v/assert kb decl 'CxUniverse)
      (v/assert kb (list 'not decl) 'CxUniverse m))
    (doall
     (for [i (range 24)
           :let [t  (symbol (str "dd_trigger" i))
                 r  (symbol (str "dd_rival" i))
                 cx (symbol (str "CxDdAt" i))
                 x  (symbol (str "DdInd" i))]]
       (do (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse m)
           (v/assert kb (list 'disjoint t r) cx m)
           (nanos (v/assert kb (list t x) cx)
                  (v/assert kb (list r x) cx)))))))

(defn- genlcx-edge-reader-fan
  "One `(genlCx sub super)` edge joining two branches of a KB carrying n **bystander**
  reader contexts — contexts that read the candidates' own branch and sit under no `sub`,
  so the edge leaves every one of their ancestor sets exactly as it found them.

  The claim is that the edge costs the readers it **widened**.  When the edge lands,
  `special/equate-under-context-edge` re-derives the functional equalities over the facts
  the widened ancestor set newly exposes, and each derivation sweeps a set of reader
  contexts: the required set is `context-down(sub)`, which here is `sub` alone, and the lazy
  one is every reader below each candidate's own storage context, which every bystander
  is.  So n moves the reader fan and leaves the widened set and the candidate set alone,
  and an edge that grows with n is the sweep re-asking readers a question already answered
  when the fact arrived.

  `genlcx_sweep_cost_test` counts the same fan in the suite; this reads it as a duration,
  which also catches a per-call cost growing inside a fan of the right size.

  **One `sub` exists at a time, and the reading retracts its own edge.**  That keeps the
  baseline out of the measurement: a `sub` per reading has to be wired somewhere it can see the candidates,
  which makes each one a bystander of every later reading — 60 of them, so the n=8 fan is
  really 68 and the n=512 fan 572, and a ratio the sweep should have made ~57x reads
  2.0x.  That is the header's own warning about a baseline that already carries the cost,
  met in the setup rather than in the sizes.  Retracting the joining edge leaves the merge
  standing (`equate-under-context-edge` says why), so every reading after the first pays
  the sweep and not the merge — which is the fan, and is the quantity this is about."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(functional gefParent) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(genlCx CxGefLeft CxUniverse) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(genlCx CxGefRight CxUniverse) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      ;; readers of the candidates' branch, under no `sub`: the joining edge changes no
      ;; ancestor set of theirs, so none of them is entitled to cost it anything
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxGefBy" i)) 'CxGefLeft) 'CxUniverse
                  {:strength :monotonic}))
      ;; the one sub, and the clashing pairs the sweep enumerates
      (v/assert kb '(genlCx CxGefSub CxGefLeft) 'CxUniverse {:strength :monotonic})
      (doseq [i (range 8)]
        (v/assert kb (list 'gefParent (symbol (str "GefK" i)) (symbol (str "GefA" i)))
                  'CxGefLeft {:strength :monotonic})
        (v/assert kb (list 'gefParent (symbol (str "GefK" i)) (symbol (str "GefB" i)))
                  'CxGefRight {:strength :monotonic})))
    (doall
     (for [_ (range readings-per-reader-fan)]
       (let [t (nanos (v/assert kb '(genlCx CxGefSub CxGefRight) 'CxUniverse
                                {:strength :monotonic}))]
         (v/retract! kb (v/handle-of kb '(genlCx CxGefSub CxGefRight) 'CxUniverse))
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

  A reading is `clashes/ranked` over what `clashes/read-clashes` answers.  Those vectors
  are in the order the candidate index answers in, so putting them in content order is
  what makes `(first (contradictions kb))` an answer about the knowledge rather than about
  which pair was typed first — and it is done at the read because a KB is written to far
  more often than it is read.  That moves the cost onto a path with no other check on it,
  which is what this is.

  `contradictions` rather than `conflicts` because a default/default pair is a dilemma;
  the two are one call, and `core/preview`'s standing filter is a third caller of it.

  The dilemmas are built under one deferred settle: they are the KB this measures
  against, not the thing being measured."
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

(defn- reader-dilemmas-beside-unseen-ones
  "`(contradictions kb CxPrdR)`, ten reads a reading, at a context holding one P/¬P
  dilemma of its own beside n standing P/¬P dilemmas placed in `CxPrdSide`, which it does
  not see.  The read takes the `contradicts` stated in what the reader sees, from the
  smaller of that extent and the `contradicts` extent (`clashes/contradictions-at`), so it
  reads none of the n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/assert kb '(genlCx CxPrdR CxUniverse) 'CxUniverse M)
    (v/assert kb '(genlCx CxPrdSide CxUniverse) 'CxUniverse M)
    (v/with-deferred-settle kb
      (v/assert kb '(prdown PRDO) 'CxPrdR {})
      (v/assert kb '(not (prdown PRDO)) 'CxPrdR {})
      (doseq [i (range n)
              :let [pr (symbol (str "prdside" i))
                    x  (symbol (str "PRDS" i))]]
        (v/assert kb (list pr x) 'CxPrdSide {})
        (v/assert kb (list 'not (list pr x)) 'CxPrdSide {})))
    (doall
     (for [_ (range 60)]
       (nanos (dotimes [_ reads-per-clash-reading]
                (count (v/contradictions kb 'CxPrdR))))))))

(defn- preview-beside-standing-dilemmas
  "`core/preview` of one fact of a predicate no nogood family reads, in the context of n
  standing P/¬P dilemmas.  The batch moves no candidate and no stamp part, so it reaches
  no reader, and the preview reads no nogood (docs/preview.md, \"Cost\").  The dilemmas
  are built under one deferred settle, as `standing-clash-reading` builds them."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [pr (symbol (str "pvread" i))
                    x  (symbol (str "PVR" i))]]
        (v/assert kb (list pr x) 'CxPerf {})
        (v/assert kb (list 'not (list pr x)) 'CxPerf {})))
    (doall
     (for [i (range 60)]
       (nanos (v/preview kb {:add [[(list 'pvLedger (symbol (str "PVA" i)) 'PVB) 'CxPerf]]}))))))

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
      (v/assert kb '(transitiveInArgInverse pi_needs_work 1 piPartOf) 'CxPerf {:strength :monotonic})
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

(defn- witness-route-search
  "One preservation support for a goal whose claim is reached by n **alternative routes**
  between the same two terms.

  The support names the routes no other route covers, and which ones decide where a
  firing over the claim is placed, so the search keeps the routes stated in the most
  general contexts (`taxonomy/general-reach-supports`).  A search that answered that by enumerating
  the routes and comparing them would be quadratic in n; the walk that ships settles each
  node once and reads each edge once, so 8x the routes is near 8x the search and nowhere
  near 64x.

  Every route is two hops through its own middle term and every edge is asserted in one
  context, so the routes tie on generality and the search is doing the work the bound is
  about rather than short-circuiting on the first general route it sees."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (v/assert kb '(transitiveInArgInverse pwNeeds 1 genl) 'CxPerf {:strength :monotonic})
      (v/assert kb '(pwNeeds pw_dog PwVal) 'CxPerf {})
      (doseq [i (range n)
              :let [m (symbol (str "pw_mid" i))]]
        (v/assert kb (list 'genl 'pw_chi m) 'CxPerf {})
        (v/assert kb (list 'genl m 'pw_dog) 'CxPerf {})))
    (let [goal '(pwNeeds pw_chi PwVal)]
      (doall (for [_ (range 60)]
               (nanos (inherit/solve-with-support kb goal 'CxPerf)))))))

(defn- genl-preserved-kb
  "n predicates `gpRel_i`, each preserved along `genl` in argument 1
  (`transitiveInArgInverse`), each with one claim `(gpRel_i gp_a_i thing)`, a forward rule
  over it, and the chain `gp_c_i` → `gp_b_i` → `gp_a_i` under `thing`: the corpus
  `genl-defeat-rejoin` and `genl-crossing-many` time a denial of `(genl gp_c_i gp_b_i)`
  over."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [t  #(symbol (str "gp_" % i))
                    pr (symbol (str "gpRel" i))]]
        (doseq [x [(t "a") (t "b") (t "c")]] (v/assert kb (list 'genl x 'thing) 'CxPerf {}))
        (v/assert kb (list 'genl (t "b") (t "a")) 'CxPerf {})
        (v/assert kb (list 'genl (t "c") (t "b")) 'CxPerf {})
        (v/assert kb (list 'transitiveInArgInverse pr 1 'genl) 'CxPerf {:strength :monotonic})
        (v/assert kb (list pr (t "a") 'thing) 'CxPerf {})
        (v/assert kb (list 'set/forwardRule (list 'implies (list pr '?x '?y) (list 'gpNoted '?x '?y)))
                  'CxPerf {})))
    kb))

(defn- genl-defeat-rejoin
  "One arriving `(not (genl …))`'s own chaining, on a KB holding n predicates each preserved
  along `genl` with a claim and a forward rule over it, and one chain of types per
  predicate that no other predicate's claim reaches.

  Every declaration here preserves along the same relation, so a `genl` edge that
  re-joined each of their rules made the arrival linear in n and n arrivals quadratic.
  `inherit/crossing-claim?` keeps the predicate whose claim sits on the edge's chain.
  Timed inside a deferred block, so each sample is the arrival's chaining and none of it
  is a settle; the narrowing reads the slot roster once per term of the edge's four-term
  closure."
  [n]
  (let [kb (genl-preserved-kb n)]
    (let [samples (volatile! [])]
      (v/with-deferred-settle kb
        (doseq [i (range n)]
          (vswap! samples conj
                  (nanos (v/assert kb (list 'not (list 'genl (symbol (str "gp_c" i)) (symbol (str "gp_b" i))))
                                   'CxPerf {:strength :monotonic})))))
      @samples)))

(defn- genl-crossing-many
  "The narrowing one `genl` denial pays, on the `genl-defeat-rejoin` corpus with n
  predicates preserved along `genl`: a batch of `inherit/moved-predicates` calls, the
  same batch at both sizes, each on a denial of a different chain's edge.

  `genl-defeat-rejoin` times whole arrivals, where the re-join dominates at its sizes;
  this times the selection alone at sizes where it would dominate.  An arrival asks it
  once from the chainer and once from the re-check triggers, and the settle asks it again
  per region member.  The narrowing reads the slot roster once per closure term and looks
  the declarations up by relation, so nothing here grows with n."
  [n]
  (let [kb (genl-preserved-kb n)]
    (let [denials (mapv #(list 'not (list 'genl (symbol (str "gp_c" %)) (symbol (str "gp_b" %))))
                        (range n))]
      (doall (for [i (range 100)]
               (nanos (dotimes [j 20]
                        (inherit/moved-predicates kb (nth denials (mod (+ i j) n))))))))))

(defn- genl-crossing-wide
  "The narrowing one `(genl gw_root gw_top)` pays, on a KB holding n subtypes of `gw_root`
  and fifty predicates preserved along `genl`, each with a claim on one of the subtypes
  and a forward rule over it: a batch of `inherit/moved-predicates` calls, the same batch
  at both sizes.

  Every claim sits below the edge, so each predicate is moved whatever the narrowing
  reads; the question is what the reading costs.  The closure below `gw_root` holds n
  terms, and past `inherit/crossing-closure-cap` the edge is not narrowed: the walk stops
  one term past the cap and every predicate preserved along `genl` is moved off the
  declarations' relation index, with no read per term.  The selection is timed alone
  because the arrival around it re-joins fifty rules, which is the same work at both
  sizes and would dilute the growth."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "gw_leaf" i)) 'gw_root) 'CxPerf {}))
      (v/assert kb '(genl gw_root thing) 'CxPerf {})
      (v/assert kb '(genl gw_top thing) 'CxPerf {})
      (doseq [j (range 50) :let [pr (symbol (str "gwRel" j))]]
        (v/assert kb (list 'transitiveInArgInverse pr 1 'genl) 'CxPerf {:strength :monotonic})
        (v/assert kb (list pr (symbol (str "gw_leaf" j)) 'thing) 'CxPerf {})
        (v/assert kb (list 'set/forwardRule (list 'implies (list pr '?x '?y) (list 'gwNoted '?x '?y)))
                  'CxPerf {})))
    (doall (for [_ (range 60)]
             (nanos (dotimes [_ 10]
                      (inherit/moved-predicates kb '(genl gw_root gw_top))))))))

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

(defn- qcn-chain-load
  "Each assert of a containment chain of n regions loaded one fact at a time, with the
  spatial prover registered and one forward rule over a calculus predicate — the
  `lein bench-qcnchain` prover + rule column, read per fact.

  Every pair of a chain composes, so each arriving fact tightens pairs network-wide.
  docs/qcn.md, \"Cost at load, measured\", says where that cost goes: the plain pass
  warm-starts and the join is semi-naive, and the support-carrying pass runs whole once
  per arriving fact."
  [n]
  (let [kb   (fresh-kb)
        node #(symbol (str "PqcReg" %))]
    (v/add-prover kb (space/spatial-prover))
    (v/assert-rule kb ['(properPartOfRegion ?x ?y)] '(pqc_contained ?x) 'CxPerf
                   {:direction :forward})
    (doall (for [i (range 1 n)]
             (nanos (v/assert kb (list 'nonTangentialProperPart (node i) (node (dec i)))
                              'CxPerf {}))))))

(defn- qcn-arrival-over-standing-firings
  "One assert of a spatial fact in a context of its own, on a KB whose forward rule over
  the calculus stands on the n(n-1)/2 firings a containment chain of n regions entails
  in a sibling context.

  The arrival moves the calculus, so every rule joining on it is queued for the settle's
  re-check; what the re-check owes a standing firing is whether a network it rests on
  turned unsatisfiable (`chain/entailment-withdrawable?`), and none did.  The sibling
  keeps the chain's network unmoved, so no pass over it runs again; the join still reads
  it, which is the growth the bound leaves room for."
  [n]
  (let [kb   (fresh-kb)
        node #(symbol (str "PqsReg" %))]
    (v/add-prover kb (space/spatial-prover))
    (doseq [c '[CxPerfQsChain CxPerfQsSide]]
      (v/assert kb (list 'genlCx c 'CxPerf) 'CxUniverse {:strength :monotonic}))
    (v/assert-rule kb ['(properPartOfRegion ?x ?y)] '(pqsIn ?x ?y) 'CxPerf
                   {:direction :forward})
    (doseq [i (range 1 n)]
      (v/assert kb (list 'nonTangentialProperPart (node i) (node (dec i))) 'CxPerfQsChain {}))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'nonTangentialProperPart (symbol (str "PqsA" i))
                                       (symbol (str "PqsB" i)))
                              'CxPerfQsSide {}))))))

(defn- qcn-arrival-over-composed-exceptions
  "One assert of a spatial fact in a context of its own, on a KB whose forward rule stands
  on n firings and carries an exception on a relation the spatial calculus answers by
  composition.

  The arrival moves the calculus, so the rule is queued and every firing's exception is
  asked again (`special/composed-exception-rules`): the re-check takes the whole rule on
  every arrival, not the firings whose pair moved.  What grows is those n level-6 asks."
  [n]
  (let [kb   (fresh-kb)
        bird #(symbol (str "PqeBird" %))]
    (v/add-prover kb (space/spatial-prover))
    (v/assert kb '(genlCx CxPerfQeSide CxPerf) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(exceptWhen (spatiallyDisconnected ?x PqeRoom)
                              (set/forwardRule (implies (and (pqe_bird ?x)) (pqe_flies ?x))))
              'CxPerf {})
    (v/assert kb '(spatiallyDisconnected PqeCage PqeRoom) 'CxPerf {})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pqe_bird (bird i)) 'CxPerf {})))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'nonTangentialProperPart (symbol (str "PqeA" i))
                                       (symbol (str "PqeB" i)))
                              'CxPerfQeSide {}))))))

(defn- qcn-arrival-beside-an-unmoved-network
  "One assert of a spatial fact in a context of its own, on a KB holding a containment
  chain of n regions in a sibling context and a forward rule over a relation the chain
  entails nowhere, so no firing stands on it.

  The arrival moves the change clock, so the chain's network is read again for the
  re-join's delta; the read equals the resident value, which stays
  (`qcn-kb/read-network`), and the delta compares no pair.  What grows is the read,
  linear in the chain's facts.  A delta compared pair by pair reads the n(n-1) pairs
  the chain closes to.  The chain is loaded under one settle, because loading it a
  fact at a time costs a pass per fact."
  [n]
  (let [kb   (fresh-kb)
        node #(symbol (str "PquReg" %))]
    (v/add-prover kb (space/spatial-prover))
    (doseq [c '[CxPerfQuChain CxPerfQuSide]]
      (v/assert kb (list 'genlCx c 'CxPerf) 'CxUniverse {:strength :monotonic}))
    (v/assert-rule kb ['(externallyConnected ?x ?y)] '(pquTouch ?x ?y) 'CxPerf
                   {:direction :forward})
    (v/with-deferred-settle kb
      (doseq [i (range 1 n)]
        (v/assert kb (list 'nonTangentialProperPart (node i) (node (dec i))) 'CxPerfQuChain {})))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'nonTangentialProperPart (symbol (str "PquA" i))
                                       (symbol (str "PquB" i)))
                              'CxPerfQuSide {}))))))

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

;; ---- a context NAT, a sign chain, a brave ask, a marked clique ------------

(defn- context-nat-existing-context
  "Facts written into n sibling day contexts of one context function that
  `contextArgSubrelation` orders, each context already minted: the sixty timed asserts
  go round the existing days.  A mint orders the new context against its siblings
  (`context-nat/reconcile-genlCx`); a fact into a context already minted creates no
  sibling pair, so what it costs does not depend on how many siblings there are.

  The contexts are built under one deferred settle: they are the KB this measures
  against, not the thing measured."
  [n]
  (let [kb  (fresh-kb)
        M   {:strength :monotonic}
        day #(list 'CxPcnDayFn 'CxMonad
                   (list 'DatetimeFn (str (.plusDays (java.time.LocalDate/of 2000 1 1) (long %)))))]
    (v/assert kb '(result CxPcnDayFn context) 'CxUniverse M)
    (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse M)
    (v/assert kb '(contextArgSubrelation CxPcnDayFn 2 subintervalOf) 'CxUniverse M)
    (v/assert kb '(pcnNote PcnYear PcnVal) '(CxPcnDayFn CxMonad (DatetimeFn "2000")) M)
    (v/with-deferred-settle kb
      (doseq [i (range n)] (v/assert kb '(pcnNote PcnDay PcnVal) (day i) M)))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pcnNote (symbol (str "Pcn" i)) 'PcnVal)
                              (day (mod i n)) M))))))

(defn- sign-chain-rebuild
  "A `qualitativeSum` chain grown one link at a time, and after each of the last sixty
  links the ask of the new tail's sign.  The write moves the change clock, so each ask
  rebuilds the sign reading (`sign/build-reading`), which reads every sign fact: linear in
  the chain by design.  What the check catches is a fixpoint that re-applies every
  constraint per pass while the chain moves one link per pass, or a narrowing that copies
  the growing support set along the chain: both are quadratic."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        q  #(symbol (str "PsQ" %))]
    (v/add-reasoner kb :sign)
    (v/assert kb '(signOf PsQ0 SignPositive) 'CxPerf M)
    (into []
          (keep (fn [i]
                  (v/assert kb (list 'signOf (symbol (str "PsP" i)) 'SignPositive) 'CxPerf M)
                  (v/assert kb (list 'qualitativeSum (q (dec i)) (symbol (str "PsP" i)) (q i))
                            'CxPerf M)
                  (when (> i (- n 60))
                    (nanos (count (v/ask kb (list 'signOf (q i) '?s) 'CxPerf))))))
          (range 1 (inc n)))))

(def ^:private asks-per-brave-reading
  "Asks batched into one timed reading, the same batch at both sizes so it cancels out of
  the ratio: a single ask answered from the held classification sits under the noise
  floor."
  10)

(defn- brave-ask-between-writes
  "`(bravely S)` and `(cautiously S)` asked of one Nixon diamond's side on a KB holding n
  independent diamonds, with no write between the asks.  Belief does not move between
  two asks, so the classification the first one computes answers the rest
  (`label/classify-datum`); a classification per ask is linear in the dilemmas.

  The solve-free path, forced by hiding the backend, so the reading does not depend on a
  solver being installed: with one, a classification over every dilemma at once is
  exponential in the independent dilemmas and would not finish at the large size.  Built
  under one deferred settle."
  [n]
  (with-redefs [solver/available? (constantly false)]
    (let [kb   (fresh-kb)
          rule (fn [ante conseq]
                 (list 'set/defaultRule
                       (list 'set/forwardRule (rules/rule-sentence [ante] conseq))))]
      (v/add-reasoner kb :brave-cautious)
      (v/assert kb (rule '(pb_quaker ?x) '(pb_pacifist ?x)) 'CxPerf)
      (v/assert kb (rule '(pb_republican ?x) '(not (pb_pacifist ?x))) 'CxPerf)
      (v/with-deferred-settle kb
        (doseq [i (range n) :let [x (symbol (str "PbX" i))]]
          (v/assert kb (list 'pb_quaker x) 'CxPerf)
          (v/assert kb (list 'pb_republican x) 'CxPerf)))
      (doall (for [_ (range 60)]
               (nanos (dotimes [_ asks-per-brave-reading]
                        (v/ask? kb '(bravely (pb_pacifist PbX0)) 'CxPerf)
                        (v/ask? kb '(cautiously (pb_pacifist PbX0)) 'CxPerf))))))))

(defn- cautious-ask-beside-unseen-dilemmas
  "`(cautiously S)` asked of one side of the Nixon diamond a reader `CxPcR` holds, beside n
  diamonds placed in `CxPcSide`, which it does not see, each ask after a write so the
  classification is rebuilt.  The classification reads the dilemmas `CxPcR` reads
  (`clashes/contradictions-at`), so it reads none of the n.  The solve-free path, forced
  by hiding the backend, as `brave-ask-between-writes` forces it.  The diamonds are built
  under one deferred settle."
  [n]
  (with-redefs [solver/available? (constantly false)]
    (let [kb   (fresh-kb)
          M    {:strength :monotonic}
          rule (fn [ante conseq]
                 (list 'set/defaultRule
                       (list 'set/forwardRule (rules/rule-sentence [ante] conseq))))]
      (v/add-reasoner kb :brave-cautious)
      (v/assert kb '(genlCx CxPcR CxUniverse) 'CxUniverse M)
      (v/assert kb '(genlCx CxPcSide CxUniverse) 'CxUniverse M)
      (v/assert kb (rule '(pc_quaker ?x) '(pc_pacifist ?x)) 'CxUniverse)
      (v/assert kb (rule '(pc_republican ?x) '(not (pc_pacifist ?x))) 'CxUniverse)
      (v/with-deferred-settle kb
        (v/assert kb '(pc_quaker PcR) 'CxPcR)
        (v/assert kb '(pc_republican PcR) 'CxPcR)
        (doseq [i (range n) :let [x (symbol (str "PcX" i))]]
          (v/assert kb (list 'pc_quaker x) 'CxPcSide)
          (v/assert kb (list 'pc_republican x) 'CxPcSide)))
      (doall (for [i (range 60)]
               (do (v/assert kb (list 'pc_mark (symbol (str "PcW" i))) 'CxPerf)
                   (nanos (v/ask? kb '(cautiously (pc_pacifist PcR)) 'CxPcR))))))))

(defn- sibling-disjoint-new-spec
  "A `sibling_disjoint` clique of n specializations, then sixty more added one at a time,
  member first: each new type already holds an instance (which also holds a type outside
  the clique), and the timed write is the `(genl s root)` edge that puts it in the clique.
  Whether a type sits under the marked parent is read off the type's own supertype
  closure; the parent's spec closure holds the whole clique and is rebuilt after every
  `genl` edge.  The clique is built under one deferred settle."
  [n]
  (let [kb  (fresh-kb)
        M   {:strength :monotonic}
        add (fn [i]
              (let [t (symbol (str "psd_s" i "_t")) x (symbol (str "PsdX" i))]
                (v/assert kb (list 'psd_benign x) 'CxPerf M)
                (v/assert kb (list t x) 'CxPerf M)
                (list 'genl t 'psd_root)))]
    (v/assert kb '(genl psd_benign thing) 'CxPerf M)
    (v/assert kb '(genl psd_root thing) 'CxPerf M)
    (v/assert kb '(sibling_disjoint psd_root) 'CxPerf M)
    (v/with-deferred-settle kb
      (doseq [i (range n)] (v/assert kb (add i) 'CxPerf M)))
    (doall (for [i (range n (+ n 60))
                 :let [edge (add i)]]
             (nanos (v/assert kb edge 'CxPerf M))))))

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

(defn- installed-image-reads
  "n `disjoint` declarations over 2n types, and one term a member of the first pair, in a
  `:disk-snapshot` KB closed and opened again, so the open installs its reasoning image.
  Each reading is 1,000 asks of `decide/synced`, each comparing the membership
  candidates' separation stamp with the taxonomy's rosters."
  [n]
  (let [dir  (doto (perf-disk-dir) (delete-tree!) (.mkdirs))
        path (.getAbsolutePath dir)
        U    'CxUniverse
        t    (fn [s i] (symbol (str s i)))]
    (try
      (let [kb (v/open-kb {:backend :disk-snapshot :dir path})]
        (v/with-deferred-settle kb
          (doseq [i (range n)]
            (v/assert kb (list 'disjoint (t "isa_" i) (t "isb_" i)) U)))
        (v/assert kb '(isa_0 ImagePair) U)
        (v/assert kb '(isb_0 ImagePair) U)
        (v/close! kb))
      (let [kb (v/open-kb {:backend :disk-snapshot :dir path})]
        (try
          (doall (for [_ (range 5)] (nanos (dotimes [_ 1000] (decide/synced kb)))))
          (finally (v/close! kb))))
      (finally (delete-tree! dir)))))

(defn- first-write-after-install
  "n readers under `CxPerfFwTop`, each holding a placed `irreflexive` self tuple stated in it,
  in a `:disk-snapshot` KB closed and opened again five times; each reading is the first
  write after an open installs the reasoning image, a fact no family reads stated where
  every reader sees it.

  ```
  CxUniverse  (irreflexive pFwSelf)   timed  (pFwLedger PFwB_j PFwC)
   └─ CxPerfFwTop
       └─ CxPerfFwR_i, i < n  (pFwSelf PFwA_i PFwA_i)
  ```

  The placed sentexes are records, and the image carries the candidate index
  (docs/nmtms.md, \"A nogood placed as a conclusion\"), so the write places no nogood
  again.  An install leaving the first write to place every reader's nogood reads here as
  growth."
  [n]
  (let [dir  (doto (perf-disk-dir) (delete-tree!) (.mkdirs))
        path (.getAbsolutePath dir)
        M    {:strength :monotonic}]
    (try
      (let [kb (v/open-kb {:backend :disk-snapshot :dir path})]
        (v/with-deferred-settle kb
          (v/assert kb '(genlCx CxPerfFwTop CxUniverse) 'CxUniverse M)
          (v/assert kb '(irreflexive pFwSelf) 'CxUniverse M)
          (doseq [i (range n)
                  :let [r (symbol (str "CxPerfFwR" i)) x (symbol (str "PFwA" i))]]
            (v/assert kb (list 'genlCx r 'CxPerfFwTop) 'CxUniverse M)
            (v/assert kb (list 'pFwSelf x x) r {})))
        (v/close! kb))
      (doall (for [j (range 5)]
               (let [kb (v/open-kb {:backend :disk-snapshot :dir path})]
                 (try
                   (nanos (v/assert kb (list 'pFwLedger (symbol (str "PFwB" j)) 'PFwC) 'CxUniverse {}))
                   (finally (v/close! kb))))))
      (finally (delete-tree! dir)))))

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

(defn- bulk-premise-mark-record-size
  "200 premises of n arguments each, written through a bulk sink at their strengths on a
  disk record store with no hot cache; each reading marks all 200 again at the same
  strengths.  The slots record every mark, so a reading reads 200 slots and pages no
  record.  A mark that pages each record reads here as growth in n, the record's size."
  [n]
  (let [dir (doto (perf-disk-dir) (delete-tree!) (.mkdirs))
        s   (drs/open-record-store (.getAbsolutePath dir) {:cache-capacity 0})]
    (try
      (let [args  (mapv #(symbol (str "PbmA" %)) (range n))
            marks (with-open [^java.io.Closeable snk (cap/sentex-sink s {})]
                    (into {} (map (fn [i]
                                    [(p/write-record! snk {:sentence (list* 'pbmFact i args)
                                                           :context 'CxPerf :strength :default})
                                     :default]))
                          (range 200)))]
        (doall (for [_ (range 60)] (nanos (p/mark-premise-batch s marks)))))
      (finally
        (drs/close! s)
        (delete-tree! dir)))))

;; ---- nogoods at a vantage ------------------------------------------------
;;
;; Each KB below states a nogood's members in two contexts and reads it at their maximal
;; common descendant, the vantage.  A check times one operation against one population
;; and asserts the cost is flat in it, or linear where the operation names the
;; population.

(def ^:private vantage-lattice
  '[[CxPlA CxUniverse] [CxPlB CxUniverse] [CxPlSide CxUniverse]
    [CxPlD CxPlA] [CxPlD CxPlB] [CxPlE CxPlD]])

(defn- vantage-kb
  "A KB holding n decided negation nogoods whose vantage is `CxPlD`, read once there.

  ```
  CxUniverse
   ├─ CxPlA     (pls_t PLS_i) :default, i < n          each nogood's loser
   ├─ CxPlB     (not (pls_t PLS_i)) :monotonic         its winner
   ├─ CxPlSide  sees neither
   └─ CxPlD sees CxPlA and CxPlB: the vantage
       └─ CxPlE
  ```"
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (doseq [[c up] vantage-lattice] (v/assert kb (list 'genlCx c up) 'CxUniverse M))
      (doseq [i (range n)
              :let [s (list 'pls_t (symbol (str "PLS" i)))]]
        (v/assert kb s 'CxPlA {})
        (v/assert kb (list 'not s) 'CxPlB M)))
    (v/believed? kb (v/assert kb '(plk_t PLK) 'CxPlA {}) 'CxPlD)
    kb))

(defn- vantage-unrelated-write
  "A fact naming no nogood member, asserted at the vantage and read there, beside n
  standing decided nogoods (`vantage-kb`)."
  [n]
  (let [kb (vantage-kb n)]
    (doall (for [j (range 60)]
             (nanos (let [h (v/assert kb (list 'plu_t (symbol (str "PLU" j))) 'CxPlD {})]
                      (v/believed? kb h 'CxPlD)))))))

(defn- listener-write-beside-defeats
  "A fact naming no nogood member, asserted under one change-feed listener, beside n
  standing decided nogoods, each loser with a two-step consequence chain.

  ```
  CxPerf  (disjoint plw_dog plw_cat) (plw_cat ?x) => (plwMeows ?x Y) => (plwNoisy ?x Y)
          (plw_dog PLW_i) :monotonic, (plw_cat PLW_i) :default, i < n
          timed  (plwColor PLWSky_j PLWBlue)
  ```

  A write's report reads the belief before the write of what the defeats its sentence can
  move reach (docs/nmtms.md, \"The published window\"); this sentence moves none."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (v/assert kb '(disjoint plw_dog plw_cat) 'CxPerf M)
      (v/assert kb '(set/forwardRule (implies (plw_cat ?x) (plwMeows ?x PLWY))) 'CxPerf M)
      (v/assert kb '(set/forwardRule (implies (plwMeows ?x ?y) (plwNoisy ?x ?y))) 'CxPerf M)
      (doseq [i (range n)
              :let [x (symbol (str "PLW" i))]]
        (v/assert kb (list 'plw_dog x) 'CxPerf M)
        (v/assert kb (list 'plw_cat x) 'CxPerf {})))
    (v/watch kb (fn [_] nil))
    (doall (for [j (range 60)]
             (nanos (v/assert kb (list 'plwColor (symbol (str "PLWSky" j)) 'PLWBlue) 'CxPerf {}))))))

(defn- genlcx-edge-beside-unreached-defeats
  "A `(genlCx CxPgeSub CxPgeUp)` edge asserted and retracted under one change-feed
  listener, beside n standing decided nogoods in CxPerf, which neither context sees.

  ```
  CxPerf     (disjoint pge_dog pge_cat)   (pge_dog PGE_i) :monotonic, (pge_cat PGE_i) :default
  CxPgeSub   CxPgeUp   (each under CxUniverse alone)
  ```

  A reporting `genlCx` write reads the belief of what the defeats placed in or seen from
  the contexts it moves reach (`settle/edge-write-seeds`), so it reads none of the n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/assert kb '(genlCx CxPgeSub CxUniverse) 'CxUniverse M)
    (v/assert kb '(genlCx CxPgeUp CxUniverse) 'CxUniverse M)
    (v/with-deferred-settle kb
      (v/assert kb '(disjoint pge_dog pge_cat) 'CxPerf M)
      (doseq [i (range n)
              :let [x (symbol (str "PGE" i))]]
        (v/assert kb (list 'pge_dog x) 'CxPerf M)
        (v/assert kb (list 'pge_cat x) 'CxPerf {})))
    (v/watch kb (fn [_] nil))
    (doall (for [_ (range 60)]
             (nanos (v/retract! kb (v/assert kb '(genlCx CxPgeSub CxPgeUp) 'CxUniverse M)))))))

(defn- vantage-dissolving-write
  "The winner of one more nogood retracted, and its loser read at the vantage, beside n
  standing decided nogoods (`vantage-kb`).  The winner is asserted again, untimed, before
  each reading."
  [n]
  (let [kb (vantage-kb n)
        s  '(pls_t PLSX)
        l  (v/assert kb s 'CxPlA {})]
    (doall (for [_ (range retract-victims)]
             (let [w (v/assert kb (list 'not s) 'CxPlB {:strength :monotonic})]
               (v/believed? kb l 'CxPlD)
               (nanos (v/retract! kb w)
                      (v/believed? kb l 'CxPlD)))))))

(defn- genl-defeat-beside-defeats
  "One `genl` edge's monotonic denial asserted, placing a defeat of the edge, and a
  membership through the edge read in its context, beside n standing defeats of other
  `genl` edges and n edges no defeat names.  The denial is retracted, untimed, after each
  reading."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [t #(symbol (str "gdb_" % i))]]
        (v/assert kb (list 'genl (t "s") (t "t")) 'CxPerf {})
        (v/assert kb (list 'not (list 'genl (t "s") (t "t"))) 'CxPerf M)
        (v/assert kb (list 'genl (t "u") (t "v")) 'CxPerf {}))
      (v/assert kb '(genl gdb_a gdb_b) 'CxPerf {})
      (v/assert kb '(gdb_a GDBX) 'CxPerf {}))
    (doall (for [_ (range retract-victims)]
             (let [d (volatile! nil)
                   t (nanos (vreset! d (v/assert kb '(not (genl gdb_a gdb_b)) 'CxPerf M))
                            (when (v/isa? kb 'GDBX 'gdb_b 'CxPerf)
                              (throw (ex-info "the defeated edge is read at its context" {}))))]
               (v/retract! kb @d)
               t)))))

(defn- defeat-beside-unreached-readers
  "One `genl` edge's monotonic denial asserted in CxPerf, placing a defeat of the edge,
  then scoped `genls` reads at twenty of n readers below CxPerf, each stating its own
  edge, whose closures the defeated edge is not in.  A standing defeat of a second edge keeps the
  `genl` filter on, and every reader's closure is read once before.  The denial is
  retracted, untimed, after each reading.

  ```
  CxPerf   (genl dur_x dur_y), its denial timed; (genl dur_s dur_t) and its denial
   └─ CxDur_i  (genl dur_a_i dur_b_i), i < n        timed  (genls dur_a_i CxDur_i) × 20
  ```"
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        rd #(symbol (str "CxDur" %))
        a  #(symbol (str "dur_a" %))]
    (v/with-deferred-settle kb
      (v/assert kb '(genl dur_s dur_t) 'CxPerf {})
      (v/assert kb '(not (genl dur_s dur_t)) 'CxPerf M)
      (v/assert kb '(genl dur_x dur_y) 'CxPerf {})
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (rd i) 'CxPerf) 'CxUniverse M)
        (v/assert kb (list 'genl (a i) (symbol (str "dur_b" i))) (rd i) {})))
    (dotimes [i n] (v/genls kb (a i) (rd i)))
    (doall (for [j (range retract-victims)]
             (let [d (v/assert kb '(not (genl dur_x dur_y)) 'CxPerf M)
                   t (nanos (dotimes [k 20]
                              (let [i (mod (+ (* 20 j) k) n)] (v/genls kb (a i) (rd i)))))]
               (v/retract! kb d)
               t)))))

(defn- justification-beside-unreached-readers
  "A second justification added to E = `(genl jbu_a jbu_b)`, which a forward rule derives
  in CxPerf from `(jbu_k JBUB)` and a monotonic denial of that fact hides there, then E
  read through at CxPerf and scoped `genls` reads at twenty of n readers below CxPerf,
  each stating its own edge, whose closures E is not in.  Every reader's closure is read
  once before.  The fact under the second justification is retracted, untimed, after
  each reading.

  ```
  CxPerf   (jbu_k ?x) => E; (jbu_k JBUB) and its denial; (jbu_k JBUA_j)
   └─ CxJbu_i  (genl jbu_c_i jbu_d_i), i < n        timed  (genls jbu_a CxPerf),
                                                           (genls jbu_c_i CxJbu_i) × 20
  ```"
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        rd #(symbol (str "CxJbu" %))
        c  #(symbol (str "jbu_c" %))]
    (v/with-deferred-settle kb
      (v/assert kb '(set/forwardRule (implies (jbu_k ?x) (genl jbu_a jbu_b))) 'CxPerf M)
      (v/assert kb '(jbu_k JBUB) 'CxPerf {})
      (v/assert kb '(not (jbu_k JBUB)) 'CxPerf M)
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (rd i) 'CxPerf) 'CxUniverse M)
        (v/assert kb (list 'genl (c i) (symbol (str "jbu_d" i))) (rd i) {})))
    (dotimes [i n] (v/genls kb (c i) (rd i)))
    (v/genls kb 'jbu_a 'CxPerf)
    (doall (for [j (range retract-victims)]
             (let [f (v/assert kb (list 'jbu_k (symbol (str "JBUA" j))) 'CxPerf {})
                   t (nanos (when-not (contains? (v/genls kb 'jbu_a 'CxPerf) 'jbu_b)
                              (throw (ex-info "the shown edge is not read at its context" {})))
                            (dotimes [k 20]
                              (let [i (mod (+ (* 20 j) k) n)] (v/genls kb (c i) (rd i)))))]
               (v/retract! kb f)
               t)))))

(defn- hidden-route-kb
  "A KB holding one claim at `hrc_c1`, a `:default` edge from it to `hrc_e` that a
  monotonic denial defeats, and n types under `hrc_e` that hold no claim, with a forward
  rule over the claim.  With `preserve?` the claim is `(hrcRel hrc_c1 HRK)`, preserved up
  `genl` at argument 1 by `transitiveInArg`, and the goal is `(hrc_noted hrc_e)`;
  without it the claim is the membership `(hrc_c1 HRK)`, the rule reads `(hrc_e ?x)`, and
  the goal is `(hrc_noted HRK)`.  Answers `[kb goal]`."
  [n preserve?]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "hrc_u" i)) 'hrc_e) 'CxPerf {}))
      (v/assert kb '(genl hrc_c1 hrc_e) 'CxPerf {})
      (if preserve?
        (do (v/assert kb '(transitiveInArg hrcRel 1 genl) 'CxPerf M)
            (v/assert kb '(hrcRel hrc_c1 HRK) 'CxPerf {})
            (v/assert kb '(set/forwardRule (implies (hrcRel ?x ?y) (hrc_noted ?x))) 'CxPerf {}))
        (do (v/assert kb '(hrc_c1 HRK) 'CxPerf {})
            (v/assert kb '(set/forwardRule (implies (hrc_e ?x) (hrc_noted ?x))) 'CxPerf {}))))
    (v/assert kb '(not (genl hrc_c1 hrc_e)) 'CxPerf M)
    [kb (if preserve? '(hrc_noted hrc_e) '(hrc_noted HRK))]))

(defn- hidden-route-beside-unclaimed-types
  "`reads-per-visibility-reading` reads of a firing whose only witness edge a placed
  defeat hides, beside n types under the edge's upper end that hold no claim
  (`hidden-route-kb`): each read searches backward for a second route and finds none."
  ([n] (hidden-route-beside-unclaimed-types n true))
  ([n preserve?]
   (let [[kb goal] (hidden-route-kb n preserve?)
         h         (v/handle-of kb goal 'CxPerf)]
     (when (v/believed? kb h 'CxPerf)
       (throw (ex-info "the hidden firing is read at its context" {})))
     (doall (for [_ (range 60)]
              (nanos (dotimes [_ reads-per-visibility-reading]
                       (v/believed? kb h 'CxPerf))))))))

(defn- hidden-route-beside-untyped-types
  "`hidden-route-beside-unclaimed-types` over a membership: the firing's goal is a type
  above the claim's, and the n types under it hold no membership of the term."
  [n]
  (hidden-route-beside-unclaimed-types n false))

(defn- hidden-route-beside-hidden-claims
  "`reads-per-visibility-reading` reads of a firing whose only witness edge a placed
  defeat hides, beside n other memberships of the same term, each under its own edge to
  the goal's type that an `except` hides: each read's backward search meets every
  membership and finds no second route.  An excepted edge fires nothing, so the firing
  keeps one justification; a membership under a defeated edge fires, and the read walks
  one justification per membership.

  ```
  CxPerf   (hrh_e ?x) => (hrh_noted ?x)
           (hrh_c HRK), (genl hrh_c hrh_e) and its denial
           (hrh_c_i HRK), (genl hrh_c_i hrh_e) and its except, i < n
                                                     timed  (believed? (hrh_noted HRK))
  ```"
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        ts (map #(symbol (str "hrh_c" %)) (range n))]
    (v/with-deferred-settle kb
      (v/assert kb '(set/forwardRule (implies (hrh_e ?x) (hrh_noted ?x))) 'CxPerf {})
      (v/assert kb '(genl hrh_c hrh_e) 'CxPerf {})
      (v/assert kb '(hrh_c HRK) 'CxPerf {})
      (doseq [t ts] (v/assert kb (list 'genl t 'hrh_e) 'CxPerf {})))
    (v/with-deferred-settle kb
      (doseq [t ts]
        (v/assert kb (list 'except (list 'sentexHandle (v/handle-of kb (list 'genl t 'hrh_e) 'CxPerf)))
                  'CxPerf)))
    (v/with-deferred-settle kb
      (doseq [t ts] (v/assert kb (list t 'HRK) 'CxPerf {})))
    (v/assert kb '(not (genl hrh_c hrh_e)) 'CxPerf M)
    (let [h (v/handle-of kb '(hrh_noted HRK) 'CxPerf)]
      (when (v/believed? kb h 'CxPerf)
        (throw (ex-info "the hidden firing is read at its context" {})))
      (doall (for [_ (range 60)]
               (nanos (dotimes [_ reads-per-visibility-reading]
                        (v/believed? kb h 'CxPerf))))))))

(defn- second-route-over-a-deep-chain
  "`reads-per-visibility-reading` reads of a firing whose witness edge, the membership's
  direct edge to the goal's type, a placed defeat hides, where the membership reaches the
  goal's type over a second route of n types: each read's backward search asks the
  membership type's ancestor set.

  ```
  CxPerf   (hrd_e ?x) => (hrd_noted ?x)
           (hrd_c HRK), (genl hrd_c hrd_e) and its denial
           (genl hrd_c hrd_t0), (genl hrd_t_i hrd_t_i+1), (genl hrd_t_n-1 hrd_e)
                                                     timed  (believed? (hrd_noted HRK))
  ```"
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        t  #(symbol (str "hrd_t" %))]
    (v/with-deferred-settle kb
      (v/assert kb '(set/forwardRule (implies (hrd_e ?x) (hrd_noted ?x))) 'CxPerf {})
      (v/assert kb '(genl hrd_c hrd_e) 'CxPerf {})
      (v/assert kb '(hrd_c HRK) 'CxPerf {}))
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl 'hrd_c (t 0)) 'CxPerf {})
      (doseq [i (range (dec n))]
        (v/assert kb (list 'genl (t i) (t (inc i))) 'CxPerf {}))
      (v/assert kb (list 'genl (t (dec n)) 'hrd_e) 'CxPerf {}))
    (v/assert kb '(not (genl hrd_c hrd_e)) 'CxPerf M)
    (let [h (v/handle-of kb '(hrd_noted HRK) 'CxPerf)]
      (when-not (v/believed? kb h 'CxPerf)
        (throw (ex-info "the firing is not read over its second route" {})))
      (doall (for [_ (range 60)]
               (nanos (dotimes [_ reads-per-visibility-reading]
                        (v/believed? kb h 'CxPerf))))))))

(defn- loser-consequences-kb
  "A KB holding one loser-to-be `(plc_src PLCX)` in `CxPlA` and m forward rules
  concluding from it, stated alternately at the vantage `CxPlD` and at `CxPlE` below it,
  so its m consequences are stored at and below the vantage.  Each consequence is a fact
  of a binary predicate of its own, so no nogood family indexes it.  With `unary?`, each
  is a membership of `PLCX` in a type of its own, and each rule has the second
  antecedent `(plcAux ?x PLCV)`, which `CxPlA` states, so no rule has the shape
  `(implies (sub ?x) (super ?x))`.  Answers `[kb loser]`."
  ([m] (loser-consequences-kb m false))
  ([m unary?]
   (let [kb (fresh-kb)
         M  {:strength :monotonic}]
     (v/with-deferred-settle kb
       (doseq [[c up] vantage-lattice] (v/assert kb (list 'genlCx c up) 'CxUniverse M))
       (when unary? (v/assert kb '(plcAux PLCX PLCV) 'CxPlA M))
       (doseq [i (range m)]
         (v/assert kb (list 'set/forwardRule
                            (if unary?
                              (list 'implies '(and (plc_src ?x) (plcAux ?x PLCV))
                                    (list (symbol (str "plcu_c" i)) '?x))
                              (list 'implies '(plc_src ?x) (list (symbol (str "plcC" i)) '?x 'PLCV))))
                   (if (even? i) 'CxPlD 'CxPlE) M)))
     [kb (v/assert kb '(plc_src PLCX) 'CxPlA {})])))

(defn- whole-beside-loser-consequences
  "A `:monotonic` denial asserted in `CxPlB`, making the nogood with the loser of
  `loser-consequences-kb` whole at the vantage, and the loser read there.  The denial is
  retracted, untimed, after each reading."
  ([m] (whole-beside-loser-consequences m false))
  ([m unary?]
   (let [[kb l] (loser-consequences-kb m unary?)]
     (doall (for [_ (range retract-victims)]
              (let [w (volatile! nil)
                    t (nanos (vreset! w (v/assert kb '(not (plc_src PLCX)) 'CxPlB
                                                  {:strength :monotonic}))
                             (v/believed? kb l 'CxPlD))]
                (v/retract! kb @w)
                (v/believed? kb l 'CxPlD)
                t))))))

(defn- whole-beside-unary-loser-consequences
  "`whole-beside-loser-consequences` over the unary consequences of
  `loser-consequences-kb`: m memberships of the loser's term."
  [m]
  (whole-beside-loser-consequences m true))

(defn- dissolving-beside-loser-consequences
  "The `:monotonic` denial of `loser-consequences-kb`'s loser retracted, dissolving the
  nogood, and the loser read at the vantage.  The denial is asserted again, untimed,
  before each reading."
  ([m] (dissolving-beside-loser-consequences m false))
  ([m unary?]
   (let [[kb l] (loser-consequences-kb m unary?)]
     (doall (for [_ (range retract-victims)]
              (let [w (v/assert kb '(not (plc_src PLCX)) 'CxPlB {:strength :monotonic})]
                (v/believed? kb l 'CxPlD)
                (nanos (v/retract! kb w)
                       (v/believed? kb l 'CxPlD))))))))

(defn- dissolving-beside-unary-loser-consequences
  "`dissolving-beside-loser-consequences` over the unary consequences of
  `loser-consequences-kb`: m memberships of the loser's term."
  [m]
  (dissolving-beside-loser-consequences m true))

(defn- vantage-context-edge-unreached
  "A `genlCx` edge from a fresh context to `CxPlSide`, beside n standing decided nogoods
  (`vantage-kb`) the edge reaches none of."
  [n]
  (let [kb (vantage-kb n)]
    (doall (for [j (range edge-writes)]
             (nanos (v/assert kb (list 'genlCx (symbol (str "CxPlN" j)) 'CxPlSide)
                              'CxUniverse {:strength :monotonic}))))))

(defn- context-edge-making-nogoods-whole
  "A `genlCx` edge giving k negation pairs a common descendant, and one member read there.

  ```
  CxUniverse
   ├─ CxPkA  (pkn_t PKN_i) :default, i < k
   └─ CxPkB  (not (pkn_t PKN_i)) :monotonic
       └─ CxPkJ_j, j < 60      timed  (genlCx CxPkJ_j CxPkA)
  ```

  Each edge makes the k pairs whole at its own `CxPkJ_j`, so k is the content the edge
  names, and the claim is a cost per nogood."
  [k]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        cx #(symbol (str "CxPkJ" %))]
    (v/with-deferred-settle kb
      (doseq [c '[CxPkA CxPkB]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse M))
      (doseq [i (range k)
              :let [s (list 'pkn_t (symbol (str "PKN" i)))]]
        (v/assert kb s 'CxPkA {})
        (v/assert kb (list 'not s) 'CxPkB M))
      (doseq [j (range 60)] (v/assert kb (list 'genlCx (cx j) 'CxPkB) 'CxUniverse M)))
    (let [h (v/handle-of kb '(pkn_t PKN0) 'CxPkA)]
      (doall (for [j (range 60)]
               (nanos (v/assert kb (list 'genlCx (cx j) 'CxPkA) 'CxUniverse M)
                      (v/believed? kb h (cx j))))))))

(def ^:private placed-pairs
  "The nogoods `context-edge-beside-placements` holds at both sizes."
  16)

(def ^:private family-shapes
  "Per nogood family, the declarations stated in `CxUniverse` and `CxPjA`, and the facts of
  nogood i stated in `CxPjA` and in `CxPjB`, each `[sentence opts]`."
  (let [M {:strength :monotonic}
        x #(symbol (str "PJX" %))]
    {:negation   {:a (fn [i] [[(list 'pjn_t (x i)) {}]])
                  :b (fn [i] [[(list 'not (list 'pjn_t (x i))) M]])}
     :membership {:decls '[(disjoint pjm_a pjm_b)]
                  :a (fn [i] [[(list 'pjm_a (x i)) {}]])
                  :b (fn [i] [[(list 'pjm_b (x i)) M]])}
     :related    {:a (fn [i] [[(list 'disjoint (symbol (str "pjr_a" i)) (symbol (str "pjr_b" i))) M]])
                  :b (fn [i] [[(list 'genl (symbol (str "pjr_a" i)) (symbol (str "pjr_b" i))) M]])}
     :tuple      {:decls '[(functionalInArg pjTup 2)]
                  :a (fn [i] [[(list 'pjTup (x i) 'PJV1) {}]])
                  :b (fn [i] [[(list 'pjTup (x i) 'PJV2) M]])}
     :arity      {:a-decls '[(arity pjAr 2)]
                  :a (fn [_] [])
                  :b (fn [i] [[(list 'pjAr (x i) (symbol (str "PJY" i)) 'PJZ) {}]])}}))

(defn- context-edge-beside-placements
  "A `genlCx` edge giving `placed-pairs` nogoods of `family` (`family-shapes`) one more
  common descendant while each nogood holds j placements, and one member read there.  The
  edge is retracted, untimed, after each reading, so j is the same at every edge.

  ```
  CxUniverse
   ├─ CxPjA  nogood i's `:a` facts, i < placed-pairs
   └─ CxPjB  nogood i's `:b` facts
       ├─ CxPjP_p, p < j     (genlCx CxPjP_p CxPjA): a placement of each nogood
       └─ CxPjE_e, e < 60    timed  (genlCx CxPjE_e CxPjA), then retracted
  ```

  The edge moves one placement of each nogood, so j is content the edge does not name.
  Under `:arity`, nogood i is a tuple held inert at every context, which no edge places."
  [family j]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        {:keys [decls a-decls a b]} (family-shapes family)
        pc #(symbol (str "CxPjP" %))
        ec #(symbol (str "CxPjE" %))]
    (v/with-deferred-settle kb
      (doseq [c '[CxPjA CxPjB]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse M))
      (doseq [d decls] (v/assert kb d 'CxUniverse M))
      (doseq [d a-decls] (v/assert kb d 'CxPjA M))
      (doseq [i (range placed-pairs)]
        (doseq [[s o] (a i)] (v/assert kb s 'CxPjA o))
        (doseq [[s o] (b i)] (v/assert kb s 'CxPjB o)))
      (doseq [c (concat (map pc (range j)) (map ec (range edge-writes)))]
        (v/assert kb (list 'genlCx c 'CxPjB) 'CxUniverse M))
      (doseq [p (range j)] (v/assert kb (list 'genlCx (pc p) 'CxPjA) 'CxUniverse M)))
    (let [[[[s]] c] (if (seq (a 0)) [(a 0) 'CxPjA] [(b 0) 'CxPjB])
          h         (v/handle-of kb s c)]
      (doall (for [e (range edge-writes)]
               (let [w (volatile! nil)
                     t (nanos (vreset! w (v/assert kb (list 'genlCx (ec e) 'CxPjA) 'CxUniverse M))
                              (v/believed? kb h (ec e)))]
                 (v/retract! kb @w)
                 t))))))

(defn- context-edge-beside-membership-nogoods
  "A `genlCx` edge from a fresh context to `CxPgSide`, which states one `genl` edge, beside
  n standing membership conflicts in CxUniverse over types that edge does not reach.

  ```
  CxUniverse  (disjoint pg_a_t pg_b_t)  (pg_a_t PG_i) (pg_b_t PG_i) :monotonic, i < n
   └─ CxPgSide  (genl pg_y_t pg_x_t)
       └─ CxPgN_j, j < 60      timed  (genlCx CxPgN_j CxPgSide)
  ```

  The edge's lower end sees nothing its upper end does not, so it can give no nogood a
  new placement, and the claim is that it places none of the n again.  Each nogood is a
  conflict, so it stores no `defeat` for the new context's read walk to read."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (v/assert kb '(genlCx CxPgSide CxUniverse) 'CxUniverse M)
      (doseq [s '[(genl pg_a_t thing) (genl pg_b_t thing) (disjoint pg_a_t pg_b_t)
                  (genl pg_x_t thing)]]
        (v/assert kb s 'CxUniverse M))
      (v/assert kb '(genl pg_y_t pg_x_t) 'CxPgSide M)
      (doseq [i (range n)
              :let [x (symbol (str "PG" i))]]
        (v/assert kb (list 'pg_a_t x) 'CxUniverse M)
        (v/assert kb (list 'pg_b_t x) 'CxUniverse M)))
    (doall (for [j (range edge-writes)]
             (nanos (v/assert kb (list 'genlCx (symbol (str "CxPgN" j)) 'CxPgSide)
                              'CxUniverse M))))))

(defn- membership-beside-held-types
  "A membership of a fresh type asserted about a term already holding n memberships of
  types no separation reaches, and retracted untimed after each reading.  With
  `separated?`, a `disjoint` declaration reaches each fresh type through a `genl` edge,
  and the term holds no type the declaration separates the fresh one from.

  ```
  CxPerf  (disjoint pmh_s pmh_r)   (pmh_u_i PMHX), i < n
          (genl pmh_f_j pmh_s) with separated?, j < 60
          timed  (pmh_f_j PMHX)
  ```

  The new membership tests its type against the term's other types only when a
  separation reaches it (`membership/add-entry`): the unreached type tests none, and the
  reached one tests n."
  ([n] (membership-beside-held-types n false))
  ([n separated?]
   (let [kb (fresh-kb)
         M  {:strength :monotonic}
         f  #(symbol (str "pmh_f" %))]
     (v/with-deferred-settle kb
       (v/assert kb '(disjoint pmh_s pmh_r) 'CxPerf M)
       (doseq [j (range retract-victims)]
         (v/assert kb (list 'genl (f j) (if separated? 'pmh_s 'thing)) 'CxPerf M))
       (doseq [i (range n)]
         (v/assert kb (list (symbol (str "pmh_u" i)) 'PMHX) 'CxPerf M)))
     (doall (for [j (range retract-victims)]
              (let [h (volatile! nil)
                    t (nanos (vreset! h (v/assert kb (list (f j) 'PMHX) 'CxPerf {})))]
                (v/retract! kb @h)
                t))))))

(defn- separated-membership-beside-held-types
  "`membership-beside-held-types` with a separation reaching each fresh type."
  [n]
  (membership-beside-held-types n true))

(defn- separation-beside-kept-terms
  "A `disjoint` declaration asserted and retracted beside n kept terms, each holding two
  memberships of types of its own that neither side of the declaration is above, and one
  term holding a type under each side.  One type of each kept term sits under a side of a
  standing separation, so a test of the term's pair reads a separation frame.

  ```
  CxPerf  (disjoint pms_c pms_e)  (genl pms_a_i pms_c)  (pms_a_i PMS_i) (pms_b_i PMS_i), i < n
          (genl pms_l pms_left) (genl pms_r pms_right) (pms_l PMSBoth) (pms_r PMSBoth)
          timed  (disjoint pms_left pms_right), asserted and retracted
  ```

  The declaration tests again the pairs holding a type at or below one of its two sides
  (`membership/sync-memberships`, `tax/separation-moves`), and no pair of the n terms."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (doseq [s '[(disjoint pms_c pms_e) (genl pms_l pms_left) (genl pms_r pms_right)
                  (pms_l PMSBoth)]]
        (v/assert kb s 'CxPerf M))
      (doseq [i (range n)
              :let [x (symbol (str "PMS" i))
                    a (symbol (str "pms_a" i))]]
        (v/assert kb (list 'genl a 'pms_c) 'CxPerf M)
        (v/assert kb (list a x) 'CxPerf M)
        (v/assert kb (list (symbol (str "pms_b" i)) x) 'CxPerf M)))
    (v/assert kb '(pms_r PMSBoth) 'CxPerf {})
    (doall (for [_ (range retract-victims)]
             (nanos (let [d (v/assert kb '(disjoint pms_left pms_right) 'CxPerf M)]
                      (v/retract! kb d)))))))

(defn- cover-beside-kept-denials
  "A `covering` declaration over fresh types asserted and retracted, beside n kept terms
  each holding a membership and a denial of types the declaration does not reach.

  ```
  CxPerf  (pkd_u_t PKD_i) (not (pkd_v_t PKD_i)), i < n
          timed  (covering pkd_w_t pkd_p_t pkd_q_t), asserted and retracted
  ```

  A cover moving, and the edges from its parts to its whole, place again the kept terms
  with a denial and a membership at or below the cover's whole or a moved edge's lower end
  (`membership/sync-memberships`), read off the index's terms by type: none of the n.
  Placing every kept term with a denial grows with n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/bulk-assert-facts! kb (for [i (range n)] (list 'pkd_u_t (symbol (str "PKD" i)))) 'CxPerf)
    (v/bulk-assert-facts! kb (for [i (range n)] (list 'not (list 'pkd_v_t (symbol (str "PKD" i)))))
                          'CxPerf)
    (doall (for [_ (range retract-victims)]
             (nanos (let [d (v/assert kb '(covering pkd_w_t pkd_p_t pkd_q_t) 'CxPerf M)]
                      (v/retract! kb d)))))))

(defn- read-below-vantage
  "A premise with no nogood in its support read at a context below the vantage, beside n
  standing decided nogoods (`vantage-kb`): `reads-per-visibility-reading` reads a
  reading, each reading at a context of its own.  With `parent` `CxPlSide`, each reading's
  context sits below a context that sees none of the n."
  ([n] (read-below-vantage n 'CxPlD))
  ([n parent]
   (let [kb (vantage-kb n)
         cx #(symbol (str "CxPlR" %))
         h  (v/assert kb '(plr_t PLR) 'CxPlA {})]
     (v/with-deferred-settle kb
       (doseq [j (range 60)]
         (v/assert kb (list 'genlCx (cx j) parent) 'CxUniverse {:strength :monotonic})))
     (doall (for [j (range 60)]
              (nanos (dotimes [_ reads-per-visibility-reading]
                       (v/believed? kb h (cx j)))))))))

(defn- hidden-check-beside-excepts
  "Twenty `belief-status` reads of one premise at the vantage, beside n standing
  `(except (sentexHandle H))` facts on decoys stated at the vantage and n standing decided
  nogoods (`vantage-kb`).  None of the excepts or nogoods names the premise."
  [n]
  (let [kb (vantage-kb n)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [d (v/assert kb (list 'plx_decoy (symbol (str "PLX" i))) 'CxPlA M)]]
        (v/assert kb (list 'except (sx/sentex-handle d)) 'CxPlD M)))
    (let [h (v/assert kb '(plh_t PLH) 'CxPlA {})]
      (v/belief-status kb h 'CxPlD)
      (doall (for [_ (range 60)]
               (nanos (dotimes [_ reads-per-visibility-reading]
                        (v/belief-status kb h 'CxPlD))))))))

(defn- chain-beside-defeats
  "A chain of d forward firings, `(pdc_l0 PDC)` through `(pdc_l<d> PDC)`, in `CxPdc`, beside
  n negation nogoods placed in `CxPdD` (sixteen by default), and the end of the chain read
  through `believed?` at sixty readers of its own.  With `:seen?` each reader sees `CxPdD`
  too.  With `:hard?` both members of each nogood are `:monotonic`, so each places a
  `(contradicts …)` and no defeat.  With `:sib?` one `siblingDisjointException` is stated
  in `CxPdc`.  With `:arity` k, `CxPdAr`, which no reader sees, binds `pdcAr` to two
  arguments and states k tuples of three, each held inert at every context.

  ```
  CxUniverse
   ├─ CxPdc   (pdc_l0 PDC) strength `s`, (pdc_l<i> ?x) => (pdc_l<i+1> ?x), i < d
   ├─ CxPdA   (pdd_t PDD_k) :default (:monotonic with :hard?), k < n
   ├─ CxPdB   (not (pdd_t PDD_k)) :monotonic
   └─ CxPdD sees CxPdA and CxPdB: each nogood's placement
  CxPdR_j sees CxPdc, and CxPdD with :seen?
  ```"
  [d s {:keys [seen? n hard? sib? arity] :or {n 16}}]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        l  #(symbol (str "pdc_l" %))
        cx #(symbol (str "CxPdR" %))]
    (v/with-deferred-settle kb
      (doseq [[c up] '[[CxPdc CxUniverse] [CxPdA CxUniverse] [CxPdB CxUniverse]
                       [CxPdD CxPdA] [CxPdD CxPdB]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse M))
      (doseq [k (range n)
              :let [f (list 'pdd_t (symbol (str "PDD" k)))]]
        (v/assert kb f 'CxPdA (if hard? M {}))
        (v/assert kb (list 'not f) 'CxPdB M))
      (when sib?
        (v/assert kb '(siblingDisjointException pdx_a pdx_b) 'CxPdc M))
      (when arity
        (v/assert kb '(genlCx CxPdAr CxUniverse) 'CxUniverse M)
        (v/assert kb '(arity pdcAr 2) 'CxPdAr M)
        (dotimes [k arity]
          (v/assert kb (list 'pdcAr (symbol (str "PDAa" k)) (symbol (str "PDAb" k)) 'PDAc) 'CxPdAr {})))
      (doseq [i (range d)]
        (v/assert kb (list 'set/forwardRule (list 'implies (list (l i) '?x) (list (l (inc i)) '?x)))
                  'CxPdc M))
      (v/assert kb (list (l 0) 'PDC) 'CxPdc {:strength s})
      (doseq [j (range 60)]
        (v/assert kb (list 'genlCx (cx j) 'CxPdc) 'CxUniverse M)
        (when seen? (v/assert kb (list 'genlCx (cx j) 'CxPdD) 'CxUniverse M))))
    (let [h (:id (first (v/sentexes-matching kb (list (l d) 'PDC) 'CxPdc)))]
      (when-not (and h (v/believed? kb h (cx 0)))
        (throw (ex-info "the chain's end is not derived" {:depth d})))
      (doall (for [j (range 60)]
               (nanos (dotimes [_ reads-per-visibility-reading]
                        (v/believed? kb h (cx j)))))))))

(defn- monotonic-chain-beside-seen-defeats
  "`chain-beside-defeats` over a `:monotonic` chain, read where every defeat is seen."
  [d]
  (chain-beside-defeats d :monotonic {:seen? true}))

(defn- default-chain-beside-many-unseen-defeats
  "`chain-beside-defeats` over a `:default` chain, read where none of 1,024 decided
  nogoods is seen: more defeats than any of the chain's supports holds handles."
  [d]
  (chain-beside-defeats d :default {:n 1024}))

(defn- default-chain-beside-unseen-contradicts
  "`chain-beside-defeats` over a `:default` chain of depth d, beside one
  `siblingDisjointException` the reader sees and sixteen placed `(contradicts …)` it does
  not see."
  [d]
  (chain-beside-defeats d :default {:hard? true :sib? true}))

(defn- default-chain-beside-unseen-arity-candidates
  "`chain-beside-defeats` over a `:default` chain of depth d, read where sixteen placed
  `(contradicts …)` are seen, beside 64 inert tuples whose binding no reader sees."
  [d]
  (chain-beside-defeats d :default {:hard? true :seen? true :arity 64}))

(defn- monotonic-read-beside-marks
  "Twenty `in?` reads of a `:monotonic` fact in `CxMh`, beside one decided negation
  nogood placed there and n `symmetric` marks stated in `CxUniverse`, which `CxMh` sees.
  The reader sees a defeat, so a read that meets the `:monotonic` handle asks whether a
  defeat it sees names a handle in the support of a permuting mark (`exc/mark-hazard?`)."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/assert kb '(genlCx CxMh CxUniverse) 'CxUniverse M)
    (v/with-deferred-settle kb
      (dotimes [i n] (v/assert kb (list 'symmetric (symbol (str "pMhSym" i))) 'CxUniverse M)))
    (v/assert kb '(mh_p MhX) 'CxMh M)
    (v/assert kb '(not (mh_p MhX)) 'CxMh {})
    (let [h (v/assert kb '(mh_q MhY) 'CxMh M)]
      (v/in? kb h)
      (doall (for [_ (range 100)]
               (nanos (dotimes [_ 20] (v/in? kb h))))))))

(defn- backward-query-beside-candidates
  "Ten `prove`s of a goal one backward rule answers, beside n `irreflexive` self tuples
  stated in a context the mark's context does not see, and one decided negation nogood.

  ```
  CxPerf      (irreflexive pbqSelf)  (pbq_a PBQ)  (pbq_a ?x) <= (pbq_b ?x), backward
  CxPerfSide  (pbqSelf PBS_i PBS_i), i < n: nogood candidates no context places
  CxPbA (pbd_t PBD) :default, CxPbB (not (pbd_t PBD)) :monotonic, CxPbD sees both
  ```

  The search filters a rule-expanded answer against the targets of the placed defeats
  (`res/defeated-index`), and reads no candidate that forms no nogood."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/with-deferred-settle kb
      (doseq [[c up] '[[CxPbA CxUniverse] [CxPbB CxUniverse] [CxPbD CxPbA] [CxPbD CxPbB]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse M))
      (v/assert kb '(pbd_t PBD) 'CxPbA {})
      (v/assert kb '(not (pbd_t PBD)) 'CxPbB M)
      (v/assert kb '(irreflexive pbqSelf) 'CxPerf M)
      (v/assert kb '(pbq_a PBQ) 'CxPerf M)
      (v/assert kb '(set/backwardRule (implies (pbq_a ?x) (pbq_b ?x))) 'CxPerf M)
      (doseq [i (range n)
              :let [x (symbol (str "PBS" i))]]
        (v/assert kb (list 'pbqSelf x x) 'CxPerfSide {})))
    (doall (for [_ (range 60)]
             (nanos (dotimes [_ 10] (count (v/prove kb '(pbq_b ?x) 'CxPerf))))))))

(def ^:private groups
  "The subsystem each check's timed operation runs in, as `{group what-it-covers}`.  A
  group name passed to `--only` runs its checks, so a change to one subsystem runs the
  checks of that subsystem."
  (array-map
   :index      "index, reads and storage: argument roots, scoped reads, the trie, the columnar and dense stores, the overlay, the durable log"
   :taxonomy   "the genl and genlCx closures and their belief moves, context cycles, stratification walks, witness walks"
   :membership "memberships, disjointness and separations, the kept terms"
   :argtypes   "arity, arg declarations and the argument-type mints"
   :tuples     "tuple marks and the constraint exposure sweeps"
   :merges     "merges and the equality partition"
   :exceptions "excepts, refused firings, exceptWhen guards"
   :clashes    "clash and negation discovery, inherited clashes, readings of the dilemmas"
   :placement  "nogood placement and the read walk: vantages, losers, defeats, the per-family placements"
   :recover    "recover and the image install"
   :inherit    "preservation along genl and its route search"
   :chaining   "forward chaining, the settle drain, the feed, retraction teardown"
   :solvers    "the solvers, the qualitative and metric calculi, the planner, kb-quality, context NATs"))

(def checks
  ;; Full runs from 2026-10-03, where the settle journals only the clash members that
  ;; entered or left, to 2026-10-10 read 0.56x-1.56x over twenty runs, against
  ;; 5.15x-10.01x on the four runs before, which read the standing set at each settle.  3x is about twice the
  ;; worst healthy reading.
  ;;
  ;; The baseline is 25 rather than 100 because it has to be a size at which almost
  ;; nothing is standing.  At 100 the baseline already carried a hundred pairs' worth of
  ;; any per-pair cost being measured, which divides out of the ratio.
  [{:name      :clash-arbitration
    :group     :clashes
    :claim     "32x the standing clashes costs under 3x per assert — a settle reads the clash members that moved, not the standing set"
    :sizes     [25 800]
    :max-ratio 3.0
    :run       clash-arbitration}

   {:name      :constraint-exposure-shared-arg
    :group     :tuples
    :claim     "asserting into a declared-asymmetric slot costs what the region holds, not what the KB does"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       constraint-exposure-shared-arg}

   ;; **Both ends measured, on full runs.**  Above: 0.74x and 1.01x, flat — the read is
   ;; the term's memberships, and n moves only the facts that state none.  Below: the
   ;; same workload with `kb/types-of` reading every fact naming the term at position 1
   ;; instead of the unary roster reads **4.77x** (0.094 against 0.450 ms/op) — a record
   ;; fetch per fact naming the term, to find the two types it holds.  The bound is the file's standing 2.0 for a flat claim: twice the
   ;; worse healthy reading, and under half the defective one at this size step.  The gap
   ;; is a claim about the 8x step and grows with it — the defective shape is linear in n
   ;; and this is not — so a wider pair would separate further and none is needed to
   ;; fail it.
   {:name      :membership-read-under-busy-term
    :group     :membership
    :claim     "a membership question is flat in the facts that name the term but state no type"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       membership-read-under-busy-term}

   ;; **Both ends measured, on a loaded machine.**  Above: 0.27x, 0.49x and 0.80x.  Below,
   ;; the trigger reading every record that names the term and filtering them on the
   ;; network, which it did before the mint roster existed, reads 3.06x, 3.95x and 6.91x:
   ;; the step is 32x rather than the file's usual 8x because at 8x the two shapes
   ;; overlapped under that load (1.74x–2.08x against 2.14x–3.83x).
   {:name      :mint-withdrawal-under-busy-term
    :group     :argtypes
    :claim     "with subsumed mints pruned, a membership is flat in the facts that name its term"
    :sizes     [250 8000]
    :max-ratio 2.0
    :run       mint-withdrawal-under-busy-term}

   ;; **Both ends measured, in one warm JVM under a load average of 21.**  Above: 0.68x,
   ;; 0.32x and 0.20x (0.35 ms against 0.24).  Below, the settle re-reading every withheld
   ;; mint kept in the refusal record on each pass, rather than reading a release off the
   ;; departing record's term, reads 10.83x and 17.47x (0.88 ms against 15.31).
   ;; The small size is 32 because at 250 the re-read already dominates the baseline and
   ;; the defective shape read 3.44x against a healthy 2.56x.
   {:name      :settle-beside-withheld-mints
    :group     :argtypes
    :claim     "with subsumed mints pruned, a settle that moves no membership is flat in the mints the KB withholds"
    :sizes     [32 4096]
    :max-ratio 2.0
    :run       settle-beside-withheld-mints}

   ;; **Both ends measured, in one JVM under a load average of 25 to 37.**  Above: 1.05x
   ;; and 0.50x (15.2 against 16.0 ms/op).  Below, the withdrawal reading every record
   ;; stored in a context under `sub` and keeping those the network holds a mint
   ;; justification for, the context-root scan the mint family replaced, reads 2.80x (9.3
   ;; against 25.9 ms/op).  The context-last read is flat here (0.83x): it walks the mint
   ;; terms, 50 at both n, and `context-edge-beside-distant-mints` is its check.
   {:name      :mints-under-context-edge
    :group     :argtypes
    :claim     "with subsumed mints pruned, a genlCx edge over contexts holding a mint each is flat in the memberships stated beside the mints"
    :sizes     [100 1600]
    :max-ratio 2.0
    :run       mints-under-context-edge}

   ;; **Both ends measured, in one JVM under a load average of 37.**  Above: 0.58x (1.04
   ;; against 0.60 ms/op).  Below, the withdrawal reading the mints by context through the
   ;; `:mint` trie alone, every mint term's node intersected with the contexts under `sub`,
   ;; reads 8.30x (0.95 against 7.91 ms/op).  That is the read the `:mint-in` leaf exists to
   ;; replace.
   {:name      :context-edge-beside-distant-mints
    :group     :argtypes
    :claim     "with subsumed mints pruned, a genlCx edge is flat in the mints stated in contexts it does not reach"
    :sizes     [500 8000]
    :max-ratio 2.0
    :run       context-edge-beside-distant-mints}

   ;; **Both ends measured, on full runs.**  Above: 1.39x, 0.90x and 1.03x.  Below, two
   ;; shapes, each implemented and run: the readers taken as every common descendant
   ;; reads **6.28x** (1.39 against 8.72 ms/op); the readers narrowed but the maxima
   ;; found by filtering the whole intersection, which `maximal-common-descendant-contexts`
   ;; did before it walked, reads **2.86x** (1.23 against 3.51).  The bound is the file's
   ;; standing 2.0 for a flat claim, under both.
   {:name      :per-reading-vantages
    :group     :placement
    :claim     "a vantage below a maximum that reads less of the grounds costs the contexts below a ground it lacks, not the lattice below the members"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       per-reading-vantages}

   ;; **Both ends measured, on full runs.**  Above: 1.11x and 0.90x, and 0.84x and 0.67x
   ;; on two trees whose join is this one.  Below: the join reading every believed step
   ;; of the functor and filtering on the term, where it reads the term's postings, reads
   ;; **3.65x** (1.72 against 6.26 ms/op).  The bound is the standing 2.0.
   {:name      :chain-join
    :group     :tuples
    :claim     "an anti_transitive chain split across three contexts is joined on its own terms, flat in the open chains beside it"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       chain-join}

   {:name      :constraint-exposure-context-edge
    :group     :tuples
    :claim     "past the instance cap, 8x the facts behind a genlCx edge costs the same"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       constraint-exposure-context-edge}

   {:name      :unrelated-fact-under-marked-kb-fanout
    :group     :tuples
    :claim     "an unrelated predicate's assert is flat in the genlCx fanout below its context, however many other predicates elsewhere carry a functional mark"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       unrelated-fact-under-marked-kb-fanout}

   {:name      :functional-in-arg-empty-determinant-sweep
    :group     :tuples
    :claim     "8x the facts under an empty-determinant functionalInArg mark costs the same per assert"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       functional-in-arg-empty-determinant-sweep}

   {:name      :defeasible-load
    :group     :chaining
    :claim     "a fact arriving through a defeasible rule costs the same at 2000 as at 250"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       defeasible-load}

   {:name      :taxonomy-depth
    :group     :taxonomy
    :claim     "a genl edge costs the same 2000 deep in a chain as 250 deep"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       taxonomy-depth}

   ;; 2026-10-16, `--only` at load 20-40: 6.50x and 6.85x with `tax/contrapositive-closure`
   ;; held in the closure memo, 37.73x and 32.37x with the walk read per call.
   {:name      :contrapositive-chain
    :group     :taxonomy
    :claim     "16x the depth of a monotonic chain with a backward denial per level costs under 14x per argue: a read walks the contrapositive closure once"
    :sizes     [8 128]
    :max-ratio 14.0
    :run       contrapositive-chain}

   {:name      :taxonomy-belief-flip
    :group     :taxonomy
    :claim     "defeating and reviving one genl edge costs the same in a 4000-edge taxonomy as in a 500-edge one"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       taxonomy-belief-flip}

   ;; The reconcile reads the supporter families per moved handle (`tax/moved-keys`).
   {:name      :taxonomy-reconcile-moved
    :group     :taxonomy
    :claim     "a belief reconcile beside 50000 genl edges costs the same per moved handle when 16000 handles move as when 1000 do"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       taxonomy-reconcile-moved}

   ;; 2026-09-30: 0.65x-0.77x healthy.  With the withdrawal stamp comparing the flat caches'
   ;; supporting contexts by `=`, every settle's compare walked the declarations: 1.26x-1.41x
   ;; alone, 2.49x in a full run.
   {:name      :flat-cache-belief-flip
    :group     :taxonomy
    :claim     "defeating and reviving one inverse declaration costs the same in a KB declaring 4000 disjoint pairs as in one declaring 500"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       flat-cache-belief-flip}

   {:name      :permuting-mark-defeat-flip
    :group     :tuples
    :claim     "defeating and reviving one symmetric mark below its 20 facts costs the same beside 4000 facts under another mark as beside 500"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       permuting-mark-defeat-flip}

   {:name      :arg-root-retrieval
    :group     :index
    :claim     "100 patterns pinning an argument after a variable are flat in the extent"
    :sizes     [400 3200]
    :max-ratio 2.0
    :run       arg-root-retrieval}

   ;; The context is the argument roots' last level, so a scoped read intersects the
   ;; contexts at the bound argument's node with the reader's ancestor set before it
   ;; reads a leaf (docs/indexing.md §2).
   {:name      :scoped-arg-read
    :group     :index
    :claim     "a scoped read of a bound argument costs what its reader sees, not the matches stored where it cannot see"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       scoped-arg-read}

   ;; The positional trie's last level is the context too, so the walk under a ground
   ;; prefix keeps the contexts in the reader's ancestor set (docs/indexing.md §2).
   {:name      :scoped-trie-prefix-read
    :group     :index
    :claim     "a scoped read led by two ground arguments costs what its reader sees, not the matches stored where it cannot see"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       scoped-trie-prefix-read}

   ;; The walk visits every value of `?v` before its context level, so a prefix whose
   ;; matches sit where the reader cannot see leads from the argument roots instead
   ;; (`res/arg-lead`, docs/indexing.md §2).
   {:name      :scoped-trie-prefix-fan-read
    :group     :index
    :claim     "a scoped read led by two ground arguments costs what its reader sees when the matches it cannot see hold n distinct values"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       scoped-trie-prefix-fan-read}

   ;; At a variable context the argument stated in the fewest contexts leads the
   ;; intersection (`res/arg-lead`, docs/indexing.md §2).
   {:name      :variable-context-prefix-read
    :group     :index
    :claim     "a read led by two ground arguments at a variable context costs its matches, not the facts one bound argument rules out"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       variable-context-prefix-read}

   ;; The predicate extent and the rule indexes end in the context, so "is a defeat
   ;; stated where R sees" and "the rules on a key R sees" read the node's contexts
   ;; intersected with R's ancestor set (docs/indexing.md).
   {:name      :scoped-defeat-read
    :group     :index
    :claim     "whether a reader sees a placed defeat costs what it sees, not the defeats stored where it cannot see"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       scoped-defeat-read}

   {:name      :scoped-rule-read
    :group     :index
    :claim     "a reader's backward candidate rules cost what it sees, not the rules stored where it cannot see"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       scoped-rule-read}

   ;; The taxonomy holds no census of the contexts that state a `genl` edge: a scoped read
   ;; reads the `genl` extent's children intersected with the reader's ancestor set.
   {:name      :scoped-genl-census
    :group     :index
    :claim     "a scoped genl read costs what its reader sees, not the contexts stating a genl edge where it cannot see"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       scoped-genl-census}

   {:name      :closure-membership
    :group     :taxonomy
    :claim     "one pair's membership in a closure already asked is flat in the chain's length"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       closure-membership}

   ;; Both ends measured with `--only`, 2026-10-02.  Healthy at a9997916: 7.91x and 7.50x
   ;; (0.15 ms against 1.15 ms).  ec457f15, building an up-closure from its parents'
   ;; closures, reads 59.5x and 61.4x (1.9 ms against 115 ms).
   {:name      :genl-closure-read
    :group     :taxonomy
    :claim     "8x the types above a fresh one costs under 16x per genls read of it — one visit per ancestor"
    :sizes     [250 2000]
    :max-ratio 16.0
    :run       genl-closure-read}

   {:name      :membership-check
    :group     :membership
    :claim     "asserting a type membership is flat in how many the KB already holds"
    :sizes     [200 1600]
    :max-ratio 2.0
    :run       membership-check}

   {:name      :disjoint-enumeration
    :group     :taxonomy
    :claim     "an open disjointness goal is flat in the vocabulary it is not about"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       disjoint-enumeration}

   {:name      :disjoint-clique-membership
    :group     :membership
    :claim     "a membership assert whose type sits in a sibling-disjoint clique is flat in the clique size"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       disjoint-clique-membership}

   {:name      :disjoint-metatype-membership
    :group     :membership
    :claim     "a membership assert whose type belongs to a disjoint_metatype is at most linear in the member count, never quadratic"
    :sizes     [500 4000]
    :max-ratio 12.0
    :run       disjoint-metatype-membership}

   {:name      :compound-probe
    :group     :index
    :claim     "100 find-sentexes on a compound are flat in the extent of the hot atom it names"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       compound-probe}

   ;; Full runs from 2026-10-03 to 2026-10-10 read 0.52x-1.61x over twenty runs, against
   ;; 6.77x-8.17x on the four runs before.  3x is about twice the worst
   ;; healthy reading.  The opposed family (`reads/stores-opposed?`) removes a different
   ;; cost, the *scan of every stored negation*, which `negation-load` below holds flat.
   ;; The baseline is 100: at 25 the reading is mostly the fixed cost of a settle.
   {:name      :negation-arbitration
    :group     :clashes
    :claim     "8x the standing P/¬P dilemmas costs under 3x per assert — a settle reads the members that moved, not the standing set"
    :sizes     [100 800]
    :max-ratio 3.0
    :run       negation-arbitration}

   ;; The inherited twins of `clash-arbitration`, and linear in the standing set: a settle
   ;; republishes, weighs and reports every standing clash.  **Both ends measured.**
   ;; Above, one context: 1.90x alone and 5.45x in a full run, 2.6 against 14.2 ms/op, of
   ;; which `preserving-nogoods` is a quarter and the weighing and the reports the rest.
   ;; Below, the pass that asked every standing clash each settle and the whole extent for
   ;; every claim written: **12.27x** (53.7 against 659 ms/op), the better of two
   ;; attempts.  The baseline carries that pass's extent sweep over the 60 timed facts
   ;; themselves, which is what holds the defective ratio near 12.  With the emptying and
   ;; the install before and after each discovery journaling every member of every clash,
   ;; 6.7x to 10.1x alone at load 13 to 25 (12.3 ms/op at n=512), against 3.3x to 5.4x
   ;; (5.4 ms/op) healthy in the same runs.  The bound is about twice the healthy reading,
   ;; and under the defective one.
   {:name      :inherited-clash-arbitration
    :group     :clashes
    :claim     "32x the standing inherited dilemmas costs under 10x per assert — carried, not asked again"
    :sizes     [16 512]
    :max-ratio 10.0
    :run       (partial inherited-clash-arbitration false)}

   ;; The split twin.  A read at `CxPW` walks the support of what it asks over every
   ;; standing clash's placed sentexes, because belief is computed from current state
   ;; (docs/nmtms.md, "Where the scaling arguments hold").  So this cost grows with
   ;; n by design.  The memo carries every clash's question: `inherit/clashing-claim` runs
   ;; twice per assert at both sizes.
   ;;
   ;; **Why the timed fact is `unrelP` and the baseline one clash.**  Healthy and defective
   ;; are both `a + b·n` per assert, and the ratio separates them only by `a/b`.  Timing a
   ;; `bigP` fact puts both near 30: the defective pass asks the whole stored `bigP`
   ;; extent, the timed facts included, for each fact written, and that sweep lands in its
   ;; `a`.  At [16 512] that shape read 11.2x to 11.6x healthy in full runs against 20.0x
   ;; defective, a separation under the 2x slack a bound needs.  A fact of `unrelP` reaches
   ;; no preserved predicate, so the defective `a` is the assert alone and its `b` the
   ;; question of every clash, and one clash keeps the healthy `b·n` out of the denominator.
   ;;
   ;; Healthy: 9.6x, 11.8x and 13.6x alone at load 23 to 34, 20.4x and 30.9x alone at load
   ;; 16, 21.9x to 43.1x in a JVM that had run the shape before (n=1 at 0.23 to 0.42 ms
   ;; against 0.45 to 1.15 cold), and 46.1x in a full run at load 9 (0.185 against 8.51
   ;; ms).  Defective, with `discovery/*incremental-preserving*` bound false: 149x, 249x and
   ;; 441x, 373 to 395 ms/op at n=512, the 149x a first run whose n=1 read 2.5 ms.  90 is
   ;; about twice the worst healthy reading and under the defective ones.
   {:name      :inherited-clash-arbitration-split
    :group     :clashes
    :claim     "512x the standing inherited clashes split across contexts costs under 90x per unrelated assert — the memo carries each clash, and `CxPW` places them again from current state"
    :sizes     [1 512]
    :max-ratio 90.0
    :run       (partial inherited-clash-arbitration true)}

   ;; The stored claims keep entries with no nogood, so a settle publishes nothing for
   ;; them and the healthy reading is the carry's map walk: 2.37x and 2.12x alone, 0.28
   ;; to 0.32 against 0.67 ms/op.  Asking every entry again when the region holds a
   ;; handle with no record reads 26.71x alone, 4.18 against 111 ms/op.  The bound is
   ;; about four times the healthy reading, and under the defective one.
   {:name      :inherited-entry-retraction
    :group     :clashes
    :claim     "32x the carried inherited-clash entries costs under 10x per unrelated retract — a retraction asks only what it moved"
    :sizes     [16 512]
    :max-ratio 10.0
    :run       inherited-entry-retraction}

   ;; The same entries, beside a `disjoint` no question of a binary claim reads.  Healthy,
   ;; the settle reads the moved key's supporter and asks no entry: 1.24x alone, 1.12
   ;; against 1.39 ms/op.  Asking every entry again when any flat-cache entry moves reads
   ;; 16.83x alone, 5.75 against 96.8 ms/op.  The bound is about four times the healthy
   ;; reading, and under the defective one.
   {:name      :inherited-entry-declaration
    :group     :clashes
    :claim     "32x the carried inherited-clash entries costs under 5x per declaration no entry reads — a flat-cache move asks only the entries that read it"
    :sizes     [16 512]
    :max-ratio 5.0
    :run       inherited-entry-declaration}

   ;; The same entries, beside an except of a fact no entry's readings rest on.  Healthy,
   ;; the settle looks the except's target closure up in the memo's inverted index and
   ;; reads no entry: 0.92x, 0.72 against 0.67 ms/op.  Testing every entry's reading
   ;; handles against the closure reads 1.56x, 0.92 against 1.44 ms/op, and asking every
   ;; entry again when any except moves 14.53x alone, 8.39 against 121.87 ms/op.
   {:name      :inherited-entry-except
    :group     :clashes
    :claim     "32x the carried inherited-clash entries costs under 2x per except no entry's question reads — an except re-asks only the entries reading what it hides"
    :sizes     [16 512]
    :max-ratio 2.0
    :run       inherited-entry-except}

   ;; Both ends measured.  Healthy: 1.00x (0.147 against 0.147 ms per claim), each question
   ;; reading the rows its reach names through the memo's extent index.  Defective, every
   ;; question filtering the whole `bigP` extent row by row: 6.98x (1.520 against 10.605
   ;; ms).  2.0 is the file's bound for a flat claim, about twice the healthy reading.
   {:name      :recover-inherited-discovery
    :group     :recover
    :claim     "8x the claims of one preserved predicate costs under 2x per claim at recover — a question reads the stored rows its reach names, not the predicate's extent"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       recover-inherited-discovery}

   ;; Both ends measured.  Healthy: 0.56x (0.261 against 0.146 ms per claim), the
   ;; discovery syncing its own candidate index once under the copy.  Defective, the copy
   ;; and the live taxonomy re-stamping one shared index at each question: 5.60x (1.004
   ;; against 5.620 ms).  2.0 is the file's bound for a flat claim.
   {:name      :recover-discovery-own-out
    :group     :recover
    :claim     "8x the preserved claims and separated members costs under 2x per claim at recover"
    :sizes     [50 400]
    :max-ratio 2.0
    :run       recover-discovery-own-out}

   ;; Both ends measured.  Healthy: 1.06x (0.164 against 0.174 ms per nogood), each
   ;; member's violations read once per re-read.  Defective, each nogood re-asking its
   ;; members' violations, `p` disjointness tests each: 2.85x (0.407 against 1.160 ms).
   ;; 2.0 is the file's bound for a flat claim.
   {:name      :recover-discovery-separated-term
    :group     :recover
    :claim     "4x the types one term holds, each pair separated, costs under 2x per nogood at recover — a re-read asks each member's violations once"
    :sizes     [12 48]
    :max-ratio 2.0
    :run       recover-discovery-separated-term}

   ;; Both ends measured 2026-10-14, load 12.  Healthy: 0.29x (0.080 against 0.023 ms per
   ;; term).  Defective, each kept term's types reading their separation frames again, each
   ;; a scan of the n members: 3.32x (0.140 against 0.465 ms).  2.0 is the file's bound for
   ;; a flat claim.
   {:name      :recover-membership-sync
    :group     :recover
    :claim     "8x the kept terms over one n-member disjoint_metatype costs under 2x per term at recover — each type's separation frame is read once per sync"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       recover-membership-sync}

   ;; Both ends measured 2026-10-03 in one warm JVM each, load 19.  Above: 0.48x, 1.23x
   ;; and 0.70x (7.73 ms against 5.41).  Below, the image carrying no decision and no
   ;; reading, so the first write decides every reader: 11.30x, 6.91x and 3.78x (4.56 ms
   ;; against 17.26).
   {:name      :first-write-after-install
    :group     :recover
    :claim     "32x the readers holding a placed nogood costs under 2x on the first write after an image install: the image carries the candidate index"
    :sizes     [8 256]
    :max-ratio 2.0
    :run       first-write-after-install}

   ;; Both ends measured.  Healthy: 0.89x (1.857 against 1.658 ms per thousand asks), the
   ;; first ask taking the taxonomy's rosters and the rest comparing by identity.
   ;; Defective, each ask comparing the image's two copies of the `disjoint` roster entry
   ;; by entry: 27.44x (5.996 against 164.528 ms).  2.0 is the file's bound for a flat claim.
   {:name      :installed-image-reads
    :group     :recover
    :claim     "32x the disjoint declarations costs under 2x per thousand candidate-index asks after an image install — the separation stamp compares by identity"
    :sizes     [50 1600]
    :max-ratio 2.0
    :run       installed-image-reads}

   {:name      :negation-load
    :group     :clashes
    :claim     "a negative fact with no positive twin costs the same at 2000 as at 250"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       negation-load}

   {:name      :negation-gate-denials
    :group     :clashes
    :claim     "16x the negative facts with no positive twin costs under 2x per unrelated assert: the negation gate is one count read"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       negation-gate-denials}

   {:name      :converse-tuple-beside-tuples
    :group     :tuples
    :claim     "16x the stored tuples of an anti_symmetric predicate, none a converse, costs under 2x per arriving tuple: the converse read is the trie path its arguments name"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       converse-tuple-beside-tuples}

   {:name      :genl-cx-edge-beside-opposed
    :group     :clashes
    :claim     "16x the bodies stored in both polarities in contexts a genlCx edge does not reach costs under 2x per edge"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       genl-cx-edge-beside-opposed}

   {:name      :feed-listener-scaling
    :group     :chaining
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
    :group     :chaining
    :claim     "retracting a fact that names no NAT is flat in the reified-NAT population it is not about"
    :sizes     [32 1024]
    :max-ratio 2.0
    :run       retract-nat-scaling}

   {:name      :columnar-fanout
    :group     :index
    :claim     "an insert into the columnar trie is flat in the fan-out of the node it lands on"
    :sizes     [4000 64000]
    :max-ratio 2.0
    :run       columnar-fanout}

   ;; Healthy, the fallback holds the vocabulary's counters and reads 0.57x under
   ;; `--only`; with the terms' slots, memberships and the taxonomy's supporters in it,
   ;; it read 24.99x.
   {:name      :roots-fallback-section
    :group     :index
    :claim     "the roots fallback a reindex leaves, which a snapshot writes and an open thaws whole, is flat in the facts"
    :sizes     [500 8000]
    :max-ratio 2.0
    :run       roots-fallback-section}

   {:name      :exception-roster-gate
    :group     :index
    :claim     "reads/watched-rule? is flat in how many rules carry an exception"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       exception-roster-gate}

   ;; Measured 2026-10-14 per batch of a positive and a negated call: 0.704 ms at 64 and
   ;; 0.690 ms at 2,048 (0.98x).  Reading every stored key per call, 1.10 ms against
   ;; 26.7 ms (24x).
   {:name      :trigger-keys-beside-rules
    :group     :index
    :claim     "rules/trigger-keys for a fact no rule reads is flat in how many antecedent keys the stored rules take"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       trigger-keys-beside-rules}

   ;; Measured 2026-10-16 per batch of 100 reads: 0.611 ms at 64 and 0.518 ms at 2,048
   ;; (0.85x).  Reading every member and walking the fan per read, 42.2 ms against
   ;; 1,404 ms (33x).
   {:name      :ground-goal-under-a-wide-fan
    :group     :index
    :claim     "a ground goal no member answers costs the same however many sub-predicates its functor has"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       ground-goal-under-a-wide-fan}

   {:name      :overlay-selectivity
    :group     :index
    :claim     "a fork's count of a flat posting is flat in the size of the base posting it inherits"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       overlay-selectivity}

   {:name      :intersect-selectivity
    :group     :index
    :claim     "narrowing a rare argument root against a hot one is flat in the hot posting's extent"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       intersect-selectivity}

   {:name      :arity-reach-trigger
    :group     :argtypes
    :claim     "a fact of a predicate whose arity is declared is flat in that predicate's extent"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       arity-reach-trigger}

   ;; Both ends measured in one warm JVM, 2026-09-29.  Above: 1.14x (0.20 ms against
   ;; 0.23).  Below, the arrival sweeping the bound predicate's extent, the retroactive
   ;; arity report a reader deciding the nogood replaced, reads 8.58x (1.59 ms against
   ;; 13.66).  3x is `irreflexive-mark-arrival`'s bound, for its reason.
   {:name      :arity-binding-arrival
    :group     :argtypes
    :claim     "32x the conforming tuples of a predicate costs under 3x per arity binding arriving over them and read through — no tuple is swept"
    :sizes     [256 8192]
    :max-ratio 3.0
    :run       arity-binding-arrival}

   ;; Measured 2026-10-10 in one warm run of the `argtypes` group: 0.83x per hundred
   ;; members, where the tree before the metatype binding read 0.20x, the edge then
   ;; recomputing no member.  No implementation walking past the metatype's members was
   ;; timed; 2x is the bound of the per-hundred checks beside it.
   {:name      :metatype-edge-arrival
    :group     :argtypes
    :claim     "8x the members of a metatype costs under 2x per member for a monotonic edge to binary_predicate arriving over them, read through and retracted"
    :sizes     [256 2048]
    :max-ratio 2.0
    :run       metatype-edge-arrival}

   ;; Both ends measured 2026-09-30.  Healthy 0.84x (0.133 ms against 0.111).  With each
   ;; binding recomputing every functor below it and rebuilding the exact lengths of every
   ;; binding, the reading is 7.00x (1.93 ms against 13.47).  2x sits between.
   {:name      :arity-binding-under-deep-chain
    :group     :argtypes
    :claim     "16x the predicates bound beside a 64-deep chain costs under 2x per binding arriving at its bottom"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       arity-binding-under-deep-chain}

   {:name      :arity-rebuild-beside-bindings
    :group     :argtypes
    :claim     "16x the arity bindings, with no tuple and no genl parent, costs under 2x at the candidate rebuild and its first read"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       arity-rebuild-beside-bindings}

   ;; Measured 2026-10-14 over a whole settle per hundred predicates: 2.1 ms at 250 and
   ;; 1.2 ms at 4,000 (0.58x).  With each predicate walking its ancestors, 104 ms against
   ;; 1,583 ms (15x).
   {:name      :arity-refresh-under-bound-chain
    :group     :argtypes
    :claim     "16x the predicates of a chain each bound in CxUniverse costs under 2x per hundred predicates at the whole arity refresh"
    :sizes     [250 4000]
    :max-ratio 2.0
    :run       arity-refresh-under-bound-chain}

   ;; Both ends measured under `--only`, 2026-10-18, load 22-38: healthy 1.05x and 1.25x
   ;; (0.196 against 0.206 ms/op).  With the negated-antecedent keys read after the spec
   ;; closure, 4.85x (0.275 against 1.332).  With the depth repair in `settle-finish`
   ;; alone, 3.60x at [256 2048] (1.213 against 4.366).
   {:name      :genl-chain-child-first-in-one-batch
    :group     :taxonomy
    :claim     "a chain of 16x the genl edges asserted child first in one batch costs under 2x per edge"
    :sizes     [256 4096]
    :max-ratio 2.0
    :run       genl-chain-child-first-in-one-batch}

   ;; Both ends measured under `--only`, 2026-10-18, load 26-34: healthy 1.26x (0.876
   ;; against 1.101 ms/op).  With the admission checks asked of a withheld mint, 4.53x
   ;; (2.678 against 12.136); with only the entry check asking them, 5.52x (1.758 against
   ;; 9.700).
   {:name      :withheld-mint-beside-covers
    :group     :argtypes
    :claim     "16x the covers of a minted type costs under 2x per fact whose mint a more specific membership withholds"
    :sizes     [16 256]
    :max-ratio 2.0
    :run       withheld-mint-beside-covers}

   ;; Measured 2026-10-14 per hundred predicates: 0.844 ms at 256 and 0.486 ms at 4,096
   ;; (0.58x).  With the lengths below each predicate held in the bounded length entries,
   ;; 2.80 ms against 30.1 ms (10.8x).
   {:name      :arity-pairs-below-a-queued-binding
    :group     :argtypes
    :claim     "16x the predicates of a chain under a queued binding costs under 2x per hundred predicates at the pair sync, past the length entries' bound"
    :sizes     [256 4096]
    :max-ratio 2.0
    :run       arity-pairs-below-a-queued-binding}

   {:name      :bound-type-load
    :group     :argtypes
    :claim     "8x the types, every one bound to a length, costs under 2x per binding arriving above bound types"
    :sizes     [400 3200]
    :max-ratio 2.0
    :run       bound-type-load}

   ;; Both ends measured 2026-10-01.  Healthy 0.95x and 0.97x (0.130 ms against 0.124,
   ;; 0.131 against 0.127).  With a walk up from each declaration's type, the reading is
   ;; 14.44x (4.56 ms against 65.86).  2x sits between.
   {:name      :declaration-rebuild
    :group     :argtypes
    :claim     "16x the declarations over a 16x deeper hierarchy costs under 2x per hundred declarations the recover rebuild re-reads"
    :sizes     [200 3200]
    :max-ratio 2.0
    :run       declaration-rebuild}

   ;; Both ends measured 2026-10-01.  Healthy 0.52x and 0.13x (0.267 ms against 0.512,
   ;; 0.291 against 2.160).  With a walk up from each waiting declaration's type, the
   ;; reading is 13.04x (5.40 ms against 70.40).  2x sits between.
   {:name      :mint-release-after-genl-move
    :group     :argtypes
    :claim     "16x the declarations waiting over a 16x deeper hierarchy costs under 2x per hundred declarations the settle after a genl edge re-asks"
    :sizes     [200 3200]
    :max-ratio 2.0
    :run       mint-release-after-genl-move}

   ;; Both ends measured 2026-10-03 under a scratch driver's `run-check`.  Healthy 1.12x
   ;; and 1.14x (8.23 ms against 9.24, 8.09 against 9.22).  With every declaration on the
   ;; predicate asked whether its type reaches `thing` per fact, 7.61x and 8.26x (19.6 ms
   ;; against 149.3, 18.1 against 149.8).  2x sits between.
   {:name      :arg-declaration-over-facts
    :group     :argtypes
    :claim     "16x the facts beside a 16x deeper declared type costs under 2x per hundred facts an arg declaration mints over"
    :sizes     [200 3200]
    :max-ratio 2.0
    :run       arg-declaration-over-facts}

   ;; Both ends measured 2026-10-03 under a scratch driver's `run-check`, on a loaded box.
   ;; Healthy 0.22x, 0.25x, 0.70x and 1.09x over four runs (1.062 ms against 0.232 at
   ;; the first).  With each membership walking its type's up-closure for declarations
   ;; and trigger keys, 7.03x (0.430 ms against 3.023).  2x sits between.
   {:name      :membership-under-deep-type
    :group     :argtypes
    :claim     "64x the ancestors above a type costs under 2x per membership asserted in it"
    :sizes     [64 4096]
    :max-ratio 2.0
    :run       membership-under-deep-type}

   ;; Both ends measured 2026-10-01.  Healthy 1.32x and 1.09x (0.498 ms against 0.658,
   ;; 0.545 against 0.596).  With a `sees?` per fact, the reading is 7.67x (1.764 ms
   ;; against 13.529).  2x sits between.
   {:name      :lift-rebuild
    :group     :argtypes
    :claim     "16x the contexts above the stating context costs under 2x per hundred facts the recover lift rebuild re-reads"
    :sizes     [4 64]
    :max-ratio 2.0
    :run       lift-rebuild}

   {:name      :plan-scaling
    :group     :solvers
    :claim     "planning one fixed conjunction is flat in the size of the KB it is planned against"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       plan-scaling}

   {:name      :solve-rule-grounding
    :group     :solvers
    :claim     "grounding a recursive solve rule costs the same per derived atom at any chain length"
    :sizes     [500 8000]
    :max-ratio 2.0
    :run       solve-rule-grounding}

   ;; Healthy 0.79x.  Walking the base's extent for the rules reads 24.80x (0.70 ms
   ;; against 17.25 a grounding).
   {:name      :label-beside-unrelated-facts
    :group     :solvers
    :claim     "32x the facts beside a do/label program costs under 2x per grounding"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       label-beside-unrelated-facts}

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
    :group     :solvers
    :claim     "the rules, extents, chains and taxonomy readings of kb-quality grow with the vocabulary, not with what the KB stores"
    :sizes     [4000 32000]
    :max-ratio 4.0
    :run       quality-report-scaling}

   ;; **The fifth reading, first factor.**  Ω(declarations) is the floor — the census reads
   ;; each one — so 8x the declarations is at least 8x the walk, and the bound is a claim
   ;; about what sits above the floor.  Healthy it reads **7.56x and 7.71x** on full runs and 7.14x
   ;; alone, and the vocabulary is fixed at both sizes, so 97% of the reading is the walk
   ;; itself: the same KB with the declarations left out costs 0.051 ms against 1.756 at
   ;; n=250.  Below it, the form a binding read exists to replace — an arity
   ;; answered off the argument-1 posting rather than off a binding read, a walk of the posting
   ;; these very declarations fill, so a census of n costs n² — reads **59.62x**,
   ;; implemented and measured on a full run rather than supposed.  15x is about twice the
   ;; healthy reading and under a third of the defective one, which is the slack the
   ;; arbitration bounds carry.
   {:name      :quality-declaration-census
    :group     :solvers
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
   ;; placed differently from every other bound here: the floor is nearly the span, so
   ;; the healthy reading starts high and twice it is 52x, which is close enough to the
   ;; defect to be a bound that admits it on a bad run.  45x is the midpoint of the measured
   ;; pair instead — 1.7x above the worst healthy reading and 1.7x under the defective one.
   {:name      :quality-declaration-depth
    :group     :solvers
    :claim     "the declarations census costs one arity reading per super-predicate, not one per super's own ancestry"
    :sizes     [8 256]
    :max-ratio 45.0
    :run       quality-declaration-depth}

   ;; The baseline is 64 for `clash-arbitration`'s reason: a retraction's own fixed cost
   ;; — the storage teardown, the settle, the feed event — has to still dominate at the
   ;; small size, or a baseline already carrying the whole-relation pass divides it back
   ;; out.  64 unrelated contexts is a graph such a pass crosses in well under that.
   {:name      :retract-context-cycle-scaling
    :group     :taxonomy
    :claim     "retracting an edge of a context cycle is flat in the context graph it is not about"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       retract-context-cycle-scaling}

   ;; The same retraction with the n contexts in one cycle, and an insert beside that
   ;; cycle: the two edits that repair a component, against a component map of n entries
   ;; they are not about.  Each repair reads its own component's members off
   ;; `:scc-members`; with the members found by inverting the whole `:scc` map instead,
   ;; `--only` read 8.90x (retract) and 6.88x (assert) at 8192 on 2026-09-28, against
   ;; 0.41x and 0.92x.  The large size is 8192 because the inversion costs about 0.25 µs
   ;; an entry (2.20 against 0.26 ms/op for the assert at 8192), and at 2048 the
   ;; inverting assert read 1.74x on one run, under the bound.
   {:name      :retract-context-cycle-beside-cycle
    :group     :taxonomy
    :claim     "retracting an edge of a context cycle is flat in the context cycles it is not about"
    :sizes     [64 8192]
    :max-ratio 2.0
    :run       (partial retract-context-cycle-scaling context-ring!)}

   {:name      :assert-context-edge-beside-cycle
    :group     :taxonomy
    :claim     "asserting a context edge is flat in the context cycles it is not about"
    :sizes     [64 8192]
    :max-ratio 2.0
    :run       assert-context-edge-beside-cycle}

   ;; A chain moved in one pass beside a held nogood: each move walks its own `:seen`, a
   ;; chain's length, so a healthy reading grows with the chain, and the bound separates
   ;; that from the square of it.  Both ends measured under `--only`, 2026-10-10, load
   ;; 20-35: with `:seen` the union of every ancestor set under the lower end, 53.25x
   ;; (0.802 against 42.684 ms/op); with one walk, 5.97x (0.319 against 1.902).
   {:name      :genlcx-chain-moved-beside-a-nogood
    :group     :chaining
    :claim     "a chain of 8x the genlCx edges moved in one pass beside a held nogood costs under 16x per edge"
    :sizes     [128 1024]
    :max-ratio 16.0
    :run       genlcx-chain-moved-beside-a-nogood}

   ;; Both ends measured under `--only`, 2026-10-18: healthy 1.02x (0.027 against 0.028
   ;; ms/op); with `chain/place-nogoods!` forcing the reach for the arity refresh alone,
   ;; 8.11x (0.238 against 1.929).
   {:name      :recover-over-a-context-chain
    :group     :recover
    :claim     "a recover over 8x the genlCx edges in one chain costs under 2x per edge when no nogood is held"
    :sizes     [256 2048]
    :max-ratio 2.0
    :run       recover-over-a-context-chain}

   ;; The baseline is 32 for `retract-nat-scaling`'s reason, which is `clash-arbitration`'s:
   ;; a retraction has a fixed cost of its own — the storage teardown, the settle, the feed
   ;; event — and the small size has to be one where that still dominates, or a baseline
   ;; already carrying a hundred merges' worth of the per-merge term divides it back out.
   ;;
   ;; The settle reconciles the taxonomy caches over the region and the data whose
   ;; supersession entry changed since the last settle (`settle/settle-finish`), so a
   ;; retraction naming no merged term carries no per-merge term: `--only` read 0.774 ->
   ;; 0.199 ms/op (0.26x) on 2026-09-28, against 5.66x with every superseded handle
   ;; handed to that reconcile.  **The bound is read off FULL runs**, where a warm JVM
   ;; halves the small size's reading and the ratio inflates from the denominator alone
   ;; (5.66x alone against 11.22x in place, same tree): 11.22x with the superseded set
   ;; re-read each settle, against 32.12x with its reconcile re-examining every entry.
   ;; 18x sits between those two readings: it bounds re-examination, and the flat
   ;; reading sits far under it.
   {:name      :closure-rule-under-departing-context-edge
    :group     :chaining
    :claim     "8x the genl facts above a departing genlCx edge costs under 16x per retraction — one full re-join of a closure rule per run, not one per genl seed"
    :sizes     [50 400]
    :max-ratio 16.0
    :run       closure-rule-under-departing-context-edge}

   ;; `--only` on 2026-10-10: 5.90x at the parent (6.3 against 37.2 ms), where each such
   ;; edge re-joined the rule over every `unary` type; 0.61x and 1.22x (3.6 against 4.4
   ;; ms) with the re-join over the types the edge moved (`special/separation-moved-types`).
   {:name      :separation-rule-under-moving-edge
    :group     :chaining
    :claim     "a genl edge under a separated type, asserted and retracted, is flat in the unary types no separation reaches beside a rule reading disjoint"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       separation-rule-under-moving-edge}

   {:name      :context-edge-retraction-beside-its-own-mint
    :group     :chaining
    :claim     "16x the facts above a departing genlCx edge costs under 4x per retraction when the only other record it removes is its own argument-type mint"
    :sizes     [50 800]
    :max-ratio 4.0
    :run       context-edge-retraction-beside-its-own-mint}

   ;; The firings a departing `genlCx` edge re-seeds.  Flat by construction: one firing
   ;; named the edge at both n.  `--only` on 2026-10-10: healthy 0.90x (1.47 against 1.33
   ;; ms/op, load 13.0), and with the ancestor set of `super` re-seeded, 5.81x (4.15
   ;; against 24.09 ms/op, load 16.4).
   {:name      :context-edge-retraction-beside-sighted-facts
    :group     :chaining
    :claim     "16x the facts a departing genlCx edge showed its sub costs under 2x per retraction when the edge's firing concluded in the sub"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       context-edge-retraction-beside-sighted-facts}

   ;; `--only` on 2026-10-07: 4.66x (16.4 -> 76.6 ms/op), linear in the filler's own n
   ;; nogoods, against 56.96x (52.5 -> 2,988 ms/op) with each departing placement
   ;; queuing its surviving partner.
   {:name      :filler-beside-clashing-fillers
    :group     :tuples
    :claim     "8x the clashing fillers of a functional subject costs under 16x per filler asserted and retracted — its own n nogoods placed and removed, not the group's n²"
    :sizes     [25 200]
    :max-ratio 16.0
    :run       filler-beside-clashing-fillers}

   ;; Full runs from 2026-10-02 to 2026-10-10 read 0.49x-1.43x over twenty-five runs.  A
   ;; reconcile re-examining every displaced spelling per settle read 5.66x under `--only`.
   ;; 3x is twice the worst healthy reading.
   {:name      :retract-merge-scaling
    :group     :merges
    :claim     "retracting a fact naming no merged term costs under 3x per 32x the standing merges — bookkeeping, not a re-examination each"
    :sizes     [32 1024]
    :max-ratio 3.0
    :run       retract-merge-scaling}

   ;; Full runs from 2026-10-02 to 2026-10-10 read 0.13x-1.86x over twenty-five runs.  A
   ;; reconcile re-examining every standing displaced spelling read 27.93x under `--only`.
   ;; 4x is twice the worst healthy reading.  At [32 1024] the two readings sit too close
   ;; to separate, which is why the large size is 4096.
   {:name      :except-merge-scaling
    :group     :merges
    :claim     "an except of a merge, asserted and retracted, costs under 4x per 128x the standing merges — the data it reaches, not every displaced spelling"
    :sizes     [32 4096]
    :max-ratio 4.0
    :run       except-merge-scaling}

   ;; Read off both ends under `--only`, 2026-09-28: 0.328 -> 10.018 ms/op (30.52x, load
   ;; average 13) and 0.355 -> 14.672 (41.33x, load average 47) with every settle reading
   ;; each reader's withdrawal again; 0.259 -> 0.192 (0.74x) and 0.258 -> 0.201 (0.78x,
   ;; load average 12) with a settle reading none.  3x sits between them, with room for a
   ;; full run's warmer small size.
   {:name      :assert-over-standing-excepts
    :group     :exceptions
    :claim     "an assert naming nothing costs under 3x per 128x the believed excepts the KB stores — the assert reads none of them"
    :sizes     [32 4096]
    :max-ratio 3.0
    :run       assert-over-standing-excepts}

   ;; Read off both ends under `--only`, 2026-09-29: 0.294 -> 8.964 ms/op (30.48x) with
   ;; each pass walking every rule's whole refusal set for the lift, mint and constraint
   ;; entries, against 0.201 -> 0.181 (0.90x) with the passes reading the kind roster.
   {:name      :assert-beside-naf-refusals
    :group     :exceptions
    :claim     "an assert naming nothing costs under 2x per 100x the refused firings the record holds — no pass walks a rule's refusals for a lift or a mint"
    :sizes     [320 32000]
    :max-ratio 2.0
    :run       assert-beside-naf-refusals}

   ;; Read off both ends under `--only`, 2026-09-30: 0.137 -> 0.091 ms/op (0.66x).  A
   ;; reader asking every firing of the rule read 0.13 -> 1.03 ms across 200 -> 12800.
   {:name      :guarded-firings-read-below
    :group     :exceptions
    :claim     "a first read below an exceptWhen rule's context costs under 2x per 16x the rule's firings when the reader sees no blocker — no firing is asked again"
    :sizes     [200 3200]
    :max-ratio 2.0
    :run       guarded-firings-read-below}

   ;; Read off both ends under `--only`, 2026-09-30: 13.065 -> 129.743 ms/op (9.93x) with
   ;; the pass re-joining the rule its seed re-chain queued, against 5.573 -> 5.960
   ;; (1.07x) with the queue read right after the sweep.  What stays is the next pass's
   ;; narrowing, a record read per firing, so 4x leaves it room.
   {:name      :released-refusal-beside-guarded-firings
    :group     :exceptions
    :claim     "a retraction releasing a firing that places a blocker costs under 4x per 16x the firings the blocked rule holds — no pass re-joins the rule over its whole extent"
    :sizes     [200 3200]
    :max-ratio 4.0
    :run       released-refusal-beside-guarded-firings}

   ;; Read off both ends under `--only`, 2026-09-28: 1.402 -> 12.857 ms/op (9.17x) with
   ;; an un-merge re-examining every displaced spelling, against 0.542 -> 0.359 (0.66x)
   ;; with the reconcile narrowed to the sentexes naming a term of the class that moved
   ;; (`special/reconcile-removed-supersession!`).  3x sits between them, with room for a
   ;; full run's warmer small size.
   {:name      :unmerge-over-standing-merges
    :group     :merges
    :claim     "an un-merge of one class costs under 3x per 32x the standing merges it does not touch — its own class, not every displaced spelling"
    :sizes     [32 1024]
    :max-ratio 3.0
    :run       unmerge-over-standing-merges}

   ;; Read off both ends under `--only`, 2026-09-28: 1.515 -> 11.591 ms/op (7.65x) with
   ;; each merge's reconcile reading the batch's whole window, against 0.328 -> 0.212
   ;; (0.65x) with the write path leaving the window to the batch's settle.  3x sits
   ;; between them.
   {:name      :deferred-merge-batch
    :group     :merges
    :claim     "a merging assert in a deferred batch costs under 3x per 8x the merges the batch holds — its own migration, not every entry the batch displaced"
    :sizes     [128 1024]
    :max-ratio 3.0
    :run       deferred-merge-batch}

   {:name      :merge-withdrawing-a-firing
    :group     :merges
    :claim     "a merge whose displaced fact fired a rule costs under 3x per 32x the standing merges whose firings were withdrawn — its own spelling's firings, not every superseded spelling's"
    :sizes     [32 1024]
    :max-ratio 3.0
    :run       merge-withdrawing-a-firing}

   ;; Flat at the file's standing 2x, and the claim is exact: an edge that reaches no
   ;; exception must cost the same whether the KB's excepted rule has fired 32 times or
   ;; 1024.  The baseline is small for the usual reason — at 32 firings the per-firing
   ;; term has barely started, so it is not sitting in the denominator.
   {:name      :genl-edge-negation-recheck
    :group     :exceptions
    :claim     "a genl edge is flat in the firing history of a negated exception it cannot reach"
    :sizes     [32 1024]
    :max-ratio 2.0
    :run       genl-edge-negation-recheck}

   ;; Flat at the file's standing 2x.  Alone, 0.53x healthy, and 7.96x with both merge
   ;; arms gated on a mark declared anywhere in the KB.
   {:name      :genl-edge-under-no-merge-mark
    :group     :merges
    :claim     "a genl edge no merge mark stands above is flat in the facts below it"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genl-edge-under-no-merge-mark}

   ;; Measured 2026-10-03 at load 50, the assert timed alone: 1.55x and 0.74x (0.27 and
   ;; 0.70 ms against 0.42 and 0.52).  With each functor under a conflict asked whether it
   ;; reaches the lower end, 4.12x (0.28 ms against 1.15).
   {:name      :genl-edge-beside-arity-conflicts
    :group     :argtypes
    :claim     "a genl edge no functor under an arity conflict is below is flat in the functors under a conflict"
    :sizes     [64 4096]
    :max-ratio 2.0
    :run       genl-edge-beside-arity-conflicts}

   {:name      :genl-edge-under-no-rule-above
    :group     :chaining
    :claim     "a genl edge no rule reads above is flat in the facts below it"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genl-edge-under-no-rule-above}

   {:name      :edge-stratification-walk
    :group     :taxonomy
    :claim     "a genl edge's stratification walk is flat in the spec closures its rules read"
    :sizes     [4 64]
    :max-ratio 2.0
    :run       edge-stratification-walk}

   {:name      :edge-stratification-unreached
    :group     :taxonomy
    :claim     "a genl edge's stratification walk is flat in the excepted rules it does not reach"
    :sizes     [8 128]
    :max-ratio 2.0
    :run       edge-stratification-unreached}

   ;; Measured 2026-10-14 per batch of 500 checks: 0.869 ms at 8 and 0.296 ms at 128
   ;; (0.34x).  Walking from every reader above the upper end, 45.9 ms against 917 ms
   ;; (20x).
   {:name      :edge-stratification-subsumed
    :group     :taxonomy
    :claim     "a genl edge the closure already holds is flat in the excepted rules reading its upper end"
    :sizes     [8 128]
    :max-ratio 2.0
    :run       edge-stratification-subsumed}

   ;; Full runs from 2026-10-05, where membership nogoods are placed where they are seen
   ;; whole and no reader decides them, to 2026-10-10 read 0.97x-1.5x over six runs,
   ;; against 11.71x-39.26x on the runs before it.  With every standing pair re-derived per
   ;; edge it read 54.2x-96.1x.  3x is twice the worst healthy reading.  The baseline is 8,
   ;; a size at which the standing set has barely started.
   {:name      :taxonomy-edge-arbitration
    :group     :clashes
    :claim     "a genl edge separating nothing costs under 3x per write at 100x the standing clashes"
    :sizes     [8 800]
    :max-ratio 3.0
    :run       taxonomy-edge-arbitration}

   ;; Full runs from 2026-10-03 to 2026-10-10 read 0.66x-1.44x over seven runs, against
   ;; 11.9x-28.2x on the runs before, which re-derived every standing pair per edge.  3x is
   ;; about twice the worst healthy reading.
   {:name      :context-edge-arbitration
    :group     :clashes
    :claim     "a genlCx edge reaching nothing costs under 3x per write at 100x the standing P/¬P dilemmas"
    :sizes     [8 800]
    :max-ratio 3.0
    :run       context-edge-arbitration}

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
    :group     :tuples
    :claim     "a genl edge under no functional or asymmetric mark is flat in the subtree it does not walk"
    :sizes     [250 2000]
    :max-ratio 2.5
    :run       (constraint-genl-edge false 4096)}

   ;; ...and the sweep the gate lets through, which is budgeted rather than free: healthy
   ;; 0.98x and 1.03x on full runs, 0.76x alone, with the cap at 100, against **7.01x** with
   ;; the cap above n, as the shipped 8192 is, where 2,000 facts sit under the cap and the reading is the subtree instead — the same reading
   ;; `constraint-exposure-context-edge` records for its own budget, and the same argument.
   ;; The two rows fail for opposite reasons: this one if the sweep stops being bounded,
   ;; the one above it if the sweep stops being gated.  The bound is the flat claim's 2.0x,
   ;; which this one can carry: the capped sweep is a constant few tenths of a millisecond
   ;; on top of the flip, and a reading with more in it bounces less.
   {:name      :constraint-genl-mark-descent
    :group     :tuples
    :claim     "past the instance cap, 8x the facts a descending mark reaches costs the same"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       (constraint-genl-edge true 100)}

   ;; Full runs from 2026-10-07 to 2026-10-10 read 17.6x-46.5x over six runs, and
   ;; 64.9x-81.8x on the runs from 2026-10-01 to 2026-10-05.  `contradictions` filtering the
   ;; standing set by cross product before ranking it reads **937.8x**, the square arriving
   ;; where the paragraph below says it does.  125x is 1.53x the worst healthy reading since
   ;; 2026-10-01 and under a seventh of the defective one.
   ;;
   ;; The read path of the standing set, and one of the two workloads here whose reading
   ;; grows with n by construction (`quality-report-scaling` is the other): a reading
   ;; returns every standing pair, so past the call's fixed cost it costs the answer's own
   ;; size, and ordering the pairs adds the log term.  A read that re-derives the pairing,
   ;; filters the standing set by cross product, or rebuilds each report from the store
   ;; per call is super-linear, and separates from that by the square rather than by a
   ;; constant.
   ;;
   ;; The KB shape is `negation-arbitration`'s, so the two are
   ;; the write cost and the read cost of one standing set and can be quoted against each
   ;; other — the comparison the ordering's placement rests on.  The header's advice about
   ;; a small baseline lands differently here and is still followed: what a large baseline
   ;; would divide out of this ratio is not a per-pair term (the per-pair term is the whole
   ;; reading) but the fixed cost of the call, and at 25 pairs that is already small.
   ;;
   ;; **What a ratio cannot see here**, since a green run should not be read as more than
   ;; it is: `nm/sort-by-content-key` builds the key once per report, a *constant*
   ;; factor over building it per comparison, and both shapes are n log n, so this is
   ;; blind to losing it.  And the regression that
   ;; puts the ordering back on the settle path is a **write**-path cost: it lands on
   ;; `negation-arbitration` and not here.
   {:name      :standing-clash-reading
    :group     :clashes
    :claim     "a reading of the standing dilemmas costs what it returns — an ordering of the standing set, not a re-derivation of it"
    :sizes     [25 800]
    :max-ratio 125.0
    :run       standing-clash-reading}

   ;; **Flat, measured from both ends** through `measure` in a scratch JVM: 0.93x and 0.96x
   ;; healthy.  A preview that reads every standing dilemma before the batch and again
   ;; after it reads 4.49x and 6.41x at this step.
   ;; Flat: the reader sees none of the n dilemmas, and the read reads only the
   ;; `contradicts` stated in what it sees.  A read that filters the KB-wide reading grows
   ;; with n.
   {:name      :reader-dilemmas-beside-unseen-ones
    :group     :clashes
    :claim     "16x the dilemmas standing outside a reader's ancestor set costs under 2x per reading of its dilemmas"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       reader-dilemmas-beside-unseen-ones}

   {:name      :preview-beside-standing-dilemmas
    :group     :clashes
    :claim     "16x the dilemmas standing in a context costs under 2x per preview of a fact there that no nogood reads"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       preview-beside-standing-dilemmas}

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
    :group     :exceptions
    :claim     "a scoped read costs what it returns, not what the KB's excepts hide"
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
    :group     :merges
    :claim     "a genlCx edge costs the readers it widened, not every reader below its candidates"
    :sizes     [8 512]
    :max-ratio 3.0
    :run       genlcx-edge-reader-fan}

   ;; The argument-type derivations a `genlCx` edge owes the facts it brings under a
   ;; declaration.  Flat by construction: the edge brings one fact under it at both n.
   ;; Calibrated from both ends under a scratch driver's `run-check`: healthy 0.68x-1.06x
   ;; (0.65-1.08 ms/op), and with the arm walking the declared extent, 4.89x (1.11 ms/op
   ;; against 5.41).
   {:name      :genlcx-edge-beside-declared-facts
    :group     :argtypes
    :claim     "64x the declared facts beside a genlCx edge's sub costs under 2x per edge"
    :sizes     [256 16384]
    :max-ratio 2.0
    :run       genlcx-edge-beside-declared-facts}

   ;; The declarations a `genlCx` edge draws over the facts it shows `sub`.  Flat by
   ;; construction: the edge newly shows `sub` no context holding a fact at both n.
   ;; Calibrated from both ends under a load average of 25 to 43: healthy 0.46x-2.6x
   ;; across five runs, the per-edge minimum flat at 0.8-1.5 ms in a scratch driver; with
   ;; the declarations drawn over every fact `super` sees, 14.6x (15.2 against 221.1
   ;; ms/op).
   {:name      :genlcx-edge-beside-seen-declared-facts
    :group     :argtypes
    :claim     "32x the declared facts a genlCx edge's sub already sees costs under 2x per edge"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       genlcx-edge-beside-seen-declared-facts}

   {:name      :genlcx-edge-showing-an-empty-context
    :group     :argtypes
    :claim     "32x the declared facts a genlCx edge's sub sees costs under 2x per edge to an empty context"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       genlcx-edge-showing-an-empty-context}

   ;; The declarations a fact arriving reads below its context.  Flat by construction:
   ;; no declaration shares a descendant with the fact's context at either n.  Calibrated
   ;; from both ends under a load average of 25 to 43: healthy 0.52x and 1.42x; with every
   ;; declaration of the predicate fetched and placed, 4.40x (1.64 against 7.23 ms/op).
   {:name      :fact-beside-distant-declarations
    :group     :argtypes
    :claim     "16x the declarations of a fact's predicate in contexts its own shares no descendant with costs under 2x per fact"
    :sizes     [32 512]
    :max-ratio 2.0
    :run       fact-beside-distant-declarations}

   ;; The mint pairs a `genlCx` edge leaving draws again.  Flat by construction: the
   ;; contexts `sub` no longer sees hold one mint at both n.  Calibrated from both ends
   ;; under a load average of 43: healthy 1.07x (34.2 against 36.6 ms/op), and with the
   ;; pairs read off every context holding a mint, 2.96x (63.8 against 188.6 ms/op).
   {:name      :genlcx-edge-leaving-beside-distant-mints
    :group     :argtypes
    :claim     "16x the mints in a context a genlCx edge does not reach costs under 2x per edge retracted"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genlcx-edge-leaving-beside-distant-mints}

   ;; The `except`s a `genlCx` edge re-checks.  Flat by construction: the edge's `super`
   ;; sees no context stating one and the edge reaches no reader at both n.  Calibrated
   ;; from both ends under a scratch driver's `run-check`: healthy 0.69x-1.01x alone and
   ;; 1.38x after the 81 checks before it (0.19 ms/op against 0.26); with the reader's
   ;; withdrawal read again on every edge, 1.98x and 2.25x in full runs (0.233 ms/op
   ;; against 0.524); with every `except` re-queued and each excepted declaration's extent
   ;; drawn again, 9.40x-9.77x alone (3.1-3.5 ms/op against 30.6-32.6).
   {:name      :genlcx-edge-beside-excepted-declarations
    :group     :exceptions
    :claim     "16x the excepted declarations beside a genlCx edge costs under 2x per edge"
    :sizes     [4 64]
    :max-ratio 2.0
    :run       genlcx-edge-beside-excepted-declarations}

   ;; The interArg derivations a trigger membership arriving after its fact owes.  Flat
   ;; by construction: the membership's term names one declared fact at both n.
   ;; Calibrated from both ends under a scratch driver's `run-check`: healthy 0.78x-0.91x
   ;; (0.39-0.80 ms/op), and with the arm reading the declared extent, 8.60x-17.30x
   ;; (0.81-2.10 ms/op against 14.0-18.1).
   {:name      :trigger-membership-beside-declared-facts
    :group     :argtypes
    :claim     "64x the declared facts beside a trigger membership costs under 2x per membership"
    :sizes     [256 16384]
    :max-ratio 2.0
    :run       trigger-membership-beside-declared-facts}

   ;; A roster declaration at a leaf context beside the memberships of its predicate
   ;; stated where the leaf does not see.  Flat by construction: the leaf sees none of them.
   {:name      :declaration-at-a-leaf-beside-unseen-memberships
    :group     :placement
    :claim     "16x the unseen memberships beside a roster declaration at a leaf costs under 2x per declaration"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       declaration-at-a-leaf-beside-unseen-memberships}

   ;; A roster declaration at a leaf beside a stating context with many children, neither
   ;; above nor below the leaf.  Flat by construction: the leaf's down-set is one context.
   ;; Calibrated from both ends under `--only`: healthy 0.85x (0.60 ms/op against 0.70), and with
   ;; the reach walking the children of the stating context, 13.19x (0.83 against 11.01).
   {:name      :declaration-at-a-leaf-beside-a-wide-stating-context
    :group     :placement
    :claim     "64x the children of an unseen stating context beside a roster declaration at a leaf costs under 2x per declaration"
    :sizes     [64 4096]
    :max-ratio 2.0
    :run       declaration-at-a-leaf-beside-a-wide-stating-context}

   ;; A roster declaration in CxUniverse reaches every stored fact of its predicate, which one
   ;; probe of the predicate extent lists.  The facts are fixed and the contexts vary, so a
   ;; reach through the ancestor sets of the contexts below CxUniverse shows as growth.
   ;; A context added before each reading retires the closure memo, and memberships stated
   ;; in CxUniverse put the declaring context among the stating ones.  Calibrated
   ;; from both ends under `--only`: healthy 0.99x (0.55 ms/op against 0.55), and with the
   ;; reach walking the contexts below CxUniverse, 3.92x (0.59 against 2.30).
   {:name      :cxuniverse-declaration-beside-bystander-contexts
    :group     :placement
    :claim     "64x the bystander contexts beside a CxUniverse roster declaration costs under 2x per declaration"
    :sizes     [64 4096]
    :max-ratio 2.0
    :run       cxuniverse-declaration-beside-bystander-contexts}

   ;; n CxUniverse roster declarations, each denied in CxUniverse, so a placed defeat every
   ;; reader sees names each one, and no denial or rule reads a declared predicate.  The roster
   ;; reading runs no `in-force?` for the n.  Both ends read warm, 20 rounds in one JVM,
   ;; 2026-10-16, load 3: healthy 1.92x to 2.31x over the last eight rounds at 554940a2e
   ;; and at the 0.26.0 cut, and full runs 1.92x to 2.25x; with the reading weighing every
   ;; declaration's defeats, 3.87x on the coldest round and 5.4x to 6.6x warm.
   {:name      :membership-clash-beside-denied-cxuniverse-declarations
    :group     :placement
    :claim     "16x the CxUniverse roster declarations denied in CxUniverse beside a membership clash costs under 3.5x per write"
    :sizes     [8 128]
    :max-ratio 3.5
    :run       membership-clash-beside-denied-cxuniverse-declarations}

   ;; A roster declaration beside n stating contexts that share one descendant with n
   ;; contexts below it, while the declaring context has n contexts below it.  Linear by
   ;; construction: the declaration reads the n stating contexts once each.  Calibrated
   ;; from both ends under `--only`: healthy 8.51x (0.52 ms/op against 4.42), and with the
   ;; reach walking both down-sets once per stating context, 155.53x (11.66 against 1813).
   {:name      :declaration-beside-stating-contexts-over-a-wide-descendant
    :group     :placement
    :claim     "16x the stating contexts and the contexts below them beside a roster declaration costs under 24x per declaration: linear, not quadratic"
    :sizes     [64 1024]
    :max-ratio 24.0
    :run       declaration-beside-stating-contexts-over-a-wide-descendant}

   ;; The seeding a `genlCx` edge owes the `genl` edges its `sub` already sees.  Flat by
   ;; construction: the edge newly connects one fact to one rule at both n.  Calibrated
   ;; from both ends under a scratch driver's `run-check`: healthy 0.40x-1.14x (0.19-0.59
   ;; ms/op), and with the seeding walking every edge `sub` sees, 28.8x (2.41 ms/op
   ;; against 69.4).
   {:name      :genlcx-edge-under-a-seen-taxonomy
    :group     :chaining
    :claim     "32x the genl edges a genlCx edge's sub already sees costs under 2x per edge"
    :sizes     [1024 32768]
    :max-ratio 2.0
    :run       genlcx-edge-under-a-seen-taxonomy}

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
    :group     :index
    :claim     "a fact reaching the durable log is flat in what the log already holds — the index WAL logs the op, not the grown value"
    :sizes     [1000 8000]
    :max-ratio 2.0
    :run       durable-fact-append}

   ;; A bulk premise mark the slots already record pages no record, so its cost per
   ;; handle is one 24-byte slot read whatever the record's size.  Calibrated from both
   ;; ends under `--only`: healthy 0.87x and 0.79x (0.214 ms/op against 0.186, 0.240
   ;; against 0.189); with every handle's record paged and thawed, 5.45x and 12.24x
   ;; (0.817 against 4.450, 0.669 against 8.184).
   {:name      :bulk-premise-mark-record-size
    :group     :index
    :claim     "a bulk premise mark the slots already record is flat in the size of the records it marks"
    :sizes     [16 512]
    :max-ratio 2.0
    :run       bulk-premise-mark-record-size}

   ;; The pair of claims docs/qcn.md's cost section opens with, and the one this file can
   ;; hold: **the read is not the pass**.  The pass is superquadratic and says so; what
   ;; residency promises is that a *repeat* consultation costs what the answer costs and
   ;; not what the KB holds.  8x the stored extent of the calculus predicate, none of it
   ;; visible from the asking context, and the reading may not follow it.
   {:name      :qcn-network-residency
    :group     :solvers
    :claim     "a repeated qualitative consultation is flat in the stored extent of the calculus it is not about"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       qcn-network-residency}

   ;; Super-quadratic in the regions (docs/qcn.md, "Cost at load, measured"): 4x the
   ;; regions reads 10.56x-19.89x over thirty-two full runs to 2026-10-10, and 9.35x under
   ;; `--only` on 2026-09-28.  A cubic pass would read 64x; 40x is twice the worst healthy
   ;; reading and under that.
   {:name      :qcn-chain-load
    :group     :solvers
    :claim     "4x the regions of a containment chain, with a forward rule over the calculus, costs under 40x per arriving fact — not a cubic pass"
    :sizes     [20 80]
    :max-ratio 40.0
    :run       qcn-chain-load}

   ;; What grows here is the join's own read of the chain's network, linear in its facts,
   ;; and not the firings.  Measured 2026-09-28 under a load average near 14: 1.868 /
   ;; 1.878 / 1.786 -> 3.898 / 4.641 / 4.157 ms (2.09x, 2.47x, 2.33x) with the delta
   ;; comparing the chain's closed pairs, 1.53x and 1.40x with the equal read kept
   ;; resident, where a settle re-deciding every standing firing reads 4.027 -> 22.379 ms
   ;; (5.56x), about 2.3 µs a firing.  3.5x sits between the firings and the rest.
   {:name      :qcn-arrival-over-standing-firings
    :group     :solvers
    :claim     "an arriving spatial fact over a satisfiable network, per 68x the standing firings of a rule on the calculus"
    :sizes     [16 128]
    :max-ratio 3.5
    :run       qcn-arrival-over-standing-firings}

   ;; Linear in the firings: the re-check an exception answered by composition owes takes
   ;; every firing of its rule on every arrival that moves the calculus (docs/exceptions.md,
   ;; "Five channels").  Measured 2026-09-28 under a load average near 25: 1.515 -> 3.205
   ;; and 1.257 -> 2.756 ms (2.12x, 2.19x), where an arrival that queued the rule for
   ;; nothing read 0.453 -> 0.741 ms.  Thirty full runs to 2026-10-10 read 1.87x-4.70x, and
   ;; one `--only` run at a load average of 20 read 7.18x.  A re-check quadratic in the
   ;; firings would read 64x; 12x sits 1.7x above the worst healthy reading.
   {:name      :qcn-arrival-over-composed-exceptions
    :group     :solvers
    :claim     "8x the standing firings of a rule excepted on a relation the calculus composes costs under 12x per arriving spatial fact — linear in the firings"
    :sizes     [16 128]
    :max-ratio 12.0
    :run       qcn-arrival-over-composed-exceptions}

   ;; The pair-by-pair delta against the read.  Measured 2026-09-28 under a load average
   ;; near 20: 1.550 -> 2.797 ms (1.80x) with the equal read kept resident, 1.677 ->
   ;; 7.176 ms (4.28x) with the delta comparing the n(n-1) closed pairs.
   {:name      :qcn-arrival-beside-an-unmoved-network
    :group     :solvers
    :claim     "an arriving spatial fact in a sibling context, per 6x the regions of a standing network it does not move"
    :sizes     [32 192]
    :max-ratio 2.5
    :run       qcn-arrival-beside-an-unmoved-network}

   ;; Not a flat claim, and the bound says which claim it is instead.  `undercut?` is a
   ;; cross-product over the claims however the reaches are answered, so the comparing is
   ;; quadratic in n whatever happens — what the memo makes linear is the *walking*, and 8x
   ;; the claims at 64x the cost is what a lost memo reads.  12x sits between the two.
   {:name      :inherit-reach-memo
    :group     :inherit
    :claim     "8x the claims reaching one term costs under 12x per ask — one reach walk per question, not one per pair of claims"
    :sizes     [8 64]
    :max-ratio 12.0
    :run       inherit-reach-memo}

   ;; The route search beside the reach walk above.  `undercut?`'s cross-product is not in
   ;; this one — the goal carries a single claim — so what n grows is the number of routes
   ;; the witness search chooses between, and a search that compared whole routes rather
   ;; than settling each node once reads 8x the routes at 64x the cost.  12x sits between
   ;; the two, for the reason the check above picks the same number.
   {:name      :witness-route-search
    :group     :taxonomy
    :claim     "8x the routes between two terms costs under 12x per preservation support — each node settled once, not each route compared"
    :sizes     [8 64]
    :max-ratio 12.0
    :run       witness-route-search}

   ;; Without `inherit/crossing-claim?` every `genl` edge re-joins the rule of every
   ;; predicate preserved along `genl`: 6.7x here, 2.3 ms against 15.3 ms an arrival.
   ;; With it an arrival re-joins its own chain's rule and reads the slot roster once per
   ;; closure term, and reads 0.99x.  4x sits between.
   {:name      :genl-defeat-rejoin
    :group     :inherit
    :claim     "8x the predicates preserved along genl costs under 4x per arriving genl denial — it re-joins the rules whose claims cross the edge, not every one"
    :sizes     [8 64]
    :max-ratio 4.0
    :run       genl-defeat-rejoin}

   ;; Calibrated from both ends, as `genl-defeat-rejoin` is.  With the narrowing reading
   ;; one argument root per declaration per closure term it grows 8.1x here, 2.9 ms against
   ;; 23.4 ms a batch of twenty; read from the closure's terms, with the declarations
   ;; looked up by relation, it reads 0.57x.  3x sits between.
   {:name      :genl-crossing-many
    :group     :inherit
    :claim     "8x the predicates preserved along genl costs under 3x per genl denial's narrowing — the reads start from the edge's closure, not from the declarations"
    :sizes     [64 512]
    :max-ratio 3.0
    :run       genl-crossing-many}

   ;; The same narrowing with no cap on the closure grows 11.2x, 65 ms against 727 ms a
   ;; batch of ten; past `inherit/crossing-closure-cap` it reads 0.72x, 1.1 ms against
   ;; 0.8 ms.  3x sits between.
   {:name      :genl-crossing-wide
    :group     :inherit
    :claim     "8x the subtypes below a genl edge costs under 3x per edge's narrowing — a closure past the cap moves every predicate off the declarations, with no read per term"
    :sizes     [600 4800]
    :max-ratio 3.0
    :run       genl-crossing-wide}

   ;; The metric twin of `qcn-network-residency`, and the bound is calibrated the way
   ;; `inherit-reach-memo` is: from both ends, on full runs.  A closure bounds every pair
   ;; of instants, so an arriving constraint is quadratic in the instant count whatever
   ;; route it takes and no memo makes it flat — what the gate defends is that the route
   ;; is a **relaxation** and not a fresh cubic pass.  At 8x the instants it reads
   ;; 12.6x-13.4x over three full runs, and 99.5x with the same check driving
   ;; `stp/close-state` instead, which is the form the bound exists to catch.  35x sits
   ;; between: 1.9 ms an arrival against 101 ms.
   {:name      :metric-closure-warm-start
    :group     :solvers
    :claim     "8x the instants costs under 35x per arriving constraint — the closure is relaxed into, not run again"
    :sizes     [50 400]
    :max-ratio 35.0
    :run       metric-closure-warm-start}

   ;; The four below are calibrated from both ends in one warm JVM per revision, under a
   ;; load average of 10 to 17 from other suites; a full run is the reading to hold them to.
   ;;
   ;; Healthy 0.86x warm and 2.28x as the first check of a fresh JVM (0.63 ms against
   ;; 1.44).  With every assert re-ordering every sibling pair it reads 154.51x (4.16 ms
   ;; against 642.07).  3x is the reader fan's bound for the same reason.
   {:name      :context-nat-existing-context
    :group     :solvers
    :claim     "16x the sibling contexts costs under 3x per fact written into an existing context NAT"
    :sizes     [16 256]
    :max-ratio 3.0
    :run       context-nat-existing-context}

   ;; Not flat: a rebuild reads every sign fact, so the reading grows with the chain.
   ;; Healthy 23.94x, 37.75x, 40.74x and 49.98x for 32x the links.  A round-robin fixpoint
   ;; with a copied support set reads 331.39x (0.25 ms against 83.12).  100x is twice the
   ;; worst healthy reading and a third of the defective one.
   {:name      :sign-chain-rebuild
    :group     :solvers
    :claim     "32x the links of a sign chain costs under 100x per ask after a write — the rebuild is linear in the sign facts, not quadratic"
    :sizes     [25 800]
    :max-ratio 100.0
    :run       sign-chain-rebuild}

   ;; Healthy 0.82x warm and 1.74x cold.  Classifying every dilemma per ask reads 11.98x
   ;; (31.29 ms against 374.93 a batch).
   {:name      :brave-ask-between-writes
    :group     :clashes
    :claim     "10x the standing dilemmas costs under 3x per brave/cautious ask with no write between"
    :sizes     [100 1000]
    :max-ratio 3.0
    :run       brave-ask-between-writes}

   ;; Healthy 0.23x under `--only`.  A classification over every dilemma of the KB reads
   ;; 11.19x (4.55 ms against 50.97).
   {:name      :cautious-ask-beside-unseen-dilemmas
    :group     :clashes
    :claim     "16x the dilemmas standing outside a reader's ancestor set costs under 2x per cautious ask there after a write"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       cautious-ask-beside-unseen-dilemmas}

   ;; Healthy 0.84x and 0.98x.  Reading the parent's spec closure per edge reads 3.11x
   ;; (0.60 ms against 1.86); the separation is narrower than the others' because the
   ;; closure walk is cheap per member, and the claim is the ordinary flat bound.
   {:name      :sibling-disjoint-new-spec
    :group     :taxonomy
    :claim     "16x the members of a sibling_disjoint clique costs under 2x per genl edge into it"
    :sizes     [256 4096]
    :max-ratio 2.0
    :run       sibling-disjoint-new-spec}

   ;; Both ends measured in one warm JVM, 2026-09-29.  Above: 1.37x and 1.12x (0.23 ms
   ;; against 0.26).  Below, the arrival reading the marked predicate's extent, the sweep
   ;; the late-mark report took before a reader decided the nogood, reads 25.12x (1.02 ms
   ;; against 25.71).  3x is about twice the worse healthy reading.
   {:name      :irreflexive-mark-arrival
    :group     :tuples
    :claim     "32x the ordinary tuples of a predicate costs under 3x per irreflexive mark arriving over it and read through — no tuple is swept"
    :sizes     [256 8192]
    :max-ratio 3.0
    :run       irreflexive-mark-arrival}

   ;; Measured 2026-10-06: 0.77x and 1.53x under `--only`, load 13 to 40; 4.33x (14.3 ms
   ;; per write at 128, 61.7 at 1024) when the report read every standing defeat's
   ;; consequences at the write entry point.
   {:name      :verdict-window-write
    :group     :placement
    :claim     "8x the consequences a standing defeat hides, each in a context of its own, costs under 2x per reported write of a tuple a mark convicts"
    :sizes     [128 1024]
    :max-ratio 2.0
    :run       verdict-window-write}

   ;; Both ends measured 2026-10-02 in one warm JVM each, beside another 40 GB JVM.
   ;; Above: 1.19x (1.41 ms against 1.67, the tail mean).  Below, each write emptying
   ;; every reader's entry and the discovery's askers decided again, 3.90x (7.62 ms
   ;; against 29.74).
   {:name      :reader-scoped-write
    :group     :placement
    :claim     "8x the readers deciding a nogood of their own costs under 2x per write a reader sees or none does"
    :sizes     [32 256]
    :max-ratio 2.0
    :run       reader-scoped-write}

   ;; Both ends measured 2026-10-03 in one warm JVM each, load 2–4.  Above: 0.99x, 0.72x
   ;; and 0.71x (0.77 ms against 0.63).  Below, the reader deciding every standing
   ;; dilemma again and installing its whole watch on every write, 6.76x, 5.81x and 8.72x
   ;; (1.32 ms against 9.14).
   {:name      :standing-nogood-write
    :group     :placement
    :claim     "16x the standing dilemmas at a reader costs under 2x per membership joining one: the write places the nogoods it reaches"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       standing-nogood-write}

   {:name      :standing-loser-write
    :group     :placement
    :claim     "16x the standing losers at a reader costs under 2x per membership joining a nogood as its loser: the reader labels the region of the loser that arrived"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       #(standing-nogood-write % {:strength :monotonic})}

   ;; Both ends measured 2026-10-02 in one warm JVM each, beside another 40 GB JVM.
   ;; Above: 0.83x and 0.56x (1.32 ms against 1.09; 1.60 against 0.90).  Below, the
   ;; closure of every candidate rebuilt, the whole reach set compared and every
   ;; candidate's record read on each write, 2.72x and 5.67x (6.80 ms against 18.51; 4.25
   ;; against 24.12).
   {:name      :candidate-write
    :group     :placement
    :claim     "8x the standing candidates costs under 2x per write adding one"
    :sizes     [1024 8192]
    :max-ratio 2.0
    :run       candidate-write}

   ;; Both ends measured 2026-10-03, three runs each in one warm JVM, load 28.  Above:
   ;; 1.62x, 0.40x and 0.51x (2.90 ms against 1.48).  Below, each family other than the
   ;; self tuples reading its whole candidate set at the reader, 4.42x, 3.97x and 4.38x
   ;; (3.74 ms against 16.39).
   {:name      :reached-reader-family-read
    :group     :placement
    :claim     "32x the candidates of four families stated where a reader does not see them costs under 2x per write placed at the reader"
    :sizes     [256 8192]
    :max-ratio 2.0
    :run       reached-reader-family-read}

   {:name      :membership-declaration-arrival
    :group     :membership
    :claim     "32x the memberships under the two types a disjoint declaration separates costs under 2x per declaration arriving over them and read through — no membership is swept"
    :sizes     [256 8192]
    :max-ratio 2.0
    :run       membership-declaration-arrival}

   ;; Both ends measured 2026-10-05 in one warm JVM each, load 50 to 60.  Above: 1.57x,
   ;; 1.49x and 1.39x (0.50 ms against 0.70).  Below, the related-types index reading
   ;; every orthogonal again and the settle placing every contradicted one again on each
   ;; edge and each separation (be2f29a6), 11.8x (16.9 ms against 199.5).  3x is about
   ;; twice the worse healthy reading.
   {:name      :edge-beside-contradicted-orthogonals
    :group     :membership
    :claim     "32x the contradicted orthogonals costs under 3x per genl edge and disjoint over fresh types — no standing orthogonal is read or placed again"
    :sizes     [32 1024]
    :max-ratio 3.0
    :run       edge-beside-contradicted-orthogonals}

   ;; Both ends measured in one warm JVM, 2026-09-29.  Above: 1.00x and 1.03x (0.38 ms per
   ;; thousand reads).  Below, the reader's losers recomputed on every read, the cache
   ;; emptied before each, reads 36.48x.
   {:name      :decided-warm-read
    :group     :placement
    :claim     "32x the self tuples a mark convicts costs under 2x per warm read of one at its reader"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       decided-warm-read}

   ;; Both ends measured 2026-10-05.  With the bound predicates rebuilt from every binding
   ;; on each read, FAIL; read off the functor's closure, PASS.  2.0 is the file's bound
   ;; for a flat claim.
   {:name      :arity-exempt-read
    :group     :argtypes
    :claim     "16x the unrelated arity bindings costs under 2x per read of a tuple whose supers bind two lengths"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       arity-exempt-read}

   ;; A scan of every standing firing per except, in place of the target's consequence
   ;; closure, reads as growth here.  2.0 is the file's bound for a flat claim.
   {:name      :except-beside-unrelated-firings
    :group     :exceptions
    :claim     "16x the standing firings that do not rest on its target costs under 2x per except asserted and retracted"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       except-beside-unrelated-firings}

   ;; Both ends measured under `--only`, 2026-10-07, load 25-75: with every except the
   ;; upper end sees re-checked and each rule on a target re-joined over its extent, 11.36x
   ;; (93.2 ms/op against 1059.0); re-checking only what the lower end did not see, 0.93x
   ;; (2.92 against 2.72), and 1.1x-1.7x in a warm probe.  The `genlCx` filter gate
   ;; (`tax/relation-filter-active?`) still grows: it reads every stored `except`'s target
   ;; once per edge, about 0.8 us each.
   {:name      :genlcx-edge-beside-seen-excepts
    :group     :exceptions
    :claim     "16x the excepts its sub already sees costs under 2x per genlCx edge asserted and retracted"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genlcx-edge-beside-seen-excepts}

   ;; Both ends measured under `--only`, 2026-10-07: with the rule re-joined over its
   ;; extent, 6.34x (15.07 ms/op against 95.58); re-joined from the target's closure,
   ;; 0.55x-2.33x under load 60-75, and 0.97x-1.03x in a warm probe.
   {:name      :genlcx-edge-revealing-one-except
    :group     :exceptions
    :claim     "16x the standing firings that do not rest on the except it reveals costs under 2x per genlCx edge asserted and retracted"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genlcx-edge-revealing-one-except}

   ;; Both ends measured under `--only`, 2026-10-10, load 20-35: with the support of every
   ;; stored `genlCx` fact probed for an `except` by the reader classes and the filter
   ;; gate, 12.46x (3.186 against 39.689 ms/op); walking forward from the one stored
   ;; target, 1.02x (0.665 against 0.681).
   {:name      :genlcx-edge-beside-stored-context-edges
    :group     :exceptions
    :claim     "64x the stored genlCx edges, beside one except no genlCx edge rests on, costs under 2x per genlCx edge asserted and retracted"
    :sizes     [64 4096]
    :max-ratio 2.0
    :run       genlcx-edge-beside-stored-context-edges}

   ;; The drain still reads each fact's posting in the edge's lower context once, to find
   ;; none below the floor, so a healthy reading grows a little with n.  Both ends measured
   ;; under `--only`, 2026-10-10: seeding and sweeping every fact of the contexts the move
   ;; shows, 16.24x (1.909 against 31.010 ms/op); below the floor alone, 2.68x (0.395
   ;; against 1.059).  6x sits between them.
   {:name      :deferred-facts-after-a-context-edge
    :group     :chaining
    :claim     "16x the facts a deferred batch asserts after its genlCx edge costs under 6x in the closing settle's drain and re-chain"
    :sizes     [16 256]
    :max-ratio 6.0
    :run       deferred-facts-after-a-context-edge}

   ;; Both ends measured under `--only`, 2026-10-06: 1.653 -> 1.746 ms/op (1.06x), against
   ;; 16.359 -> 178.728 (10.93x) with the swept firing unrecorded and the rule re-chained
   ;; over its extent.
   {:name      :except-of-a-guard-blocker
    :group     :exceptions
    :claim     "an except of a guard's blocker, asserted and retracted, costs under 2x per 16x the guarded rule's other firings — the swept firing is released from the refusal record"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       except-of-a-guard-blocker}

   ;; Both ends measured under `--only`, 2026-10-10: 1.316 -> 980.675 ms/op (745.21x)
   ;; with a guard defeat's read reading the firing's guard coverage, against 0.174 ->
   ;; 0.356 (2.05x) with it left out (a guard defeat's force reads its blockers alone,
   ;; `except/guard-seen-fn`).
   {:name      :guard-defeats-at-a-reader
    :group     :exceptions
    :claim     "2x the guard defeats a reader sees naming one firing costs under 4x per read of the firing there — a guard defeat's read does not read the firing's guard coverage again"
    :sizes     [4 8]
    :max-ratio 4.0
    :run       guard-defeats-at-a-reader}

   ;; Both ends measured under `--only`, 2026-10-10: 24.788 -> 262.013 ms/op (10.57x)
   ;; with a source datum re-checking and re-joining every rule any SupportingProver
   ;; answers, against 0.382 -> 0.530 (1.39x) with the rules narrowed to the answers of
   ;; the provers reading the datum's predicate.
   {:name      :source-datum-beside-computed-firings
    :group     :chaining
    :claim     "a datum on a source predicate no prover of a rule's computed antecedent reads costs under 2x per 16x the rule's firings"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       source-datum-beside-computed-firings}

   ;; Both ends measured 2026-10-01.  Healthy 0.89x (1.076 ms against 0.954).  With every
   ;; candidate tuple's record read and its functor's binding asked per tuple, 3.86x
   ;; (1.269 ms against 4.894).  2.0 is the file's bound for a flat claim.
   {:name      :held-shape-first-withdrawal
    :group     :placement
    :claim     "16x the candidate tuples a reader's own binding holds, beside 200 convicted self tuples, costs under 2x per read of a convicted tuple at the reader"
    :sizes     [400 6400]
    :max-ratio 2.0
    :run       held-shape-first-withdrawal}

   ;; Both ends measured 2026-09-30 under a load average of 10 to 14.  Healthy 0.68x (0.44
   ;; ms against 0.30).  With every pair in two contexts found and recorded as standing by
   ;; each settle, the reading is 3.01x (3.67 ms against 11.06).  2x sits between the two.
   {:name      :negation-reader-write
    :group     :placement
    :claim     "8x the negation pairs placed at a reader costs under 2x per unrelated assert"
    :sizes     [100 800]
    :max-ratio 2.0
    :run       negation-reader-write}

   ;; Measured 2026-10-07 under a load average of 16 to 20: 1.10x (0.078 ms against 0.086
   ;; per pair).  2.0 is the file's bound for a flat claim.
   {:name      :recover-negation-pairs
    :group     :recover
    :claim     "8x the negation pairs costs under 2x per pair at recover — the closing settle places the queued bodies"
    :sizes     [100 800]
    :max-ratio 2.0
    :run       recover-negation-pairs}

   ;; Both ends measured 2026-10-10 under a load average of 20 to 40.  Healthy 1.17x (0.19
   ;; ms against 0.23).  With every tree type expanded: 5.28x (0.49 ms against 2.60).
   {:name      :witness-walk-beside-side-ancestors
    :group     :taxonomy
    :claim     "8x the types off the target's down-closure a breadth-first walk would reach first costs under 2x per witness walk"
    :sizes     [200 1600]
    :max-ratio 2.0
    :run       witness-walk-beside-side-ancestors}

   ;; Both ends measured 2026-10-11 at 1600 nogoods, eight warm rounds in one JVM, load
   ;; average 7 to 15.  Healthy 0.99x to 1.43x (0.090 ms against 0.100).  With each
   ;; nogood walking its own subsumptions: 5.29x to 7.54x (1.07 ms against 5.85).  At 200
   ;; nogoods a healthy settle read 1.72x to 2.09x, since the eight walks' share of a
   ;; nogood's cost is eight times larger there.
   {:name      :recover-placement-walk
    :group     :recover
    :claim     "8x the types each subsumption climbs costs under 2.5x per nogood in the settle that places what a rebuilt candidate index queued"
    :sizes     [20 160]
    :max-ratio 2.5
    :run       recover-placement-walk}

   ;; Both ends measured 2026-10-07 under a load average of 16 to 20.  Healthy 1.56x (0.66
   ;; ms against 1.03).  With the pairs placed by the first write instead of the recover:
   ;; 7.44x (2.72 ms against 20.21).
   {:name      :first-write-after-recover
    :group     :recover
    :claim     "8x the negation pairs a recover placed costs under 2x per first unrelated assert after it"
    :sizes     [100 800]
    :max-ratio 2.0
    :run       first-write-after-recover}

   ;; Both ends measured 2026-09-30.  Healthy 0.81x-1.01x (0.24 ms against 0.21-0.24),
   ;; the unmarked twin's 0.22-0.24 ms at 32768.  With the functional checks reading the
   ;; slot `(P a b ?v)` by intersecting the two hubs' argument roots it reads 2.78x-3.05x
   ;; (0.23 ms against 0.65-0.74), and with the determinant read scanning one argument
   ;; root 7.53x.  Before the determinant read, a tuple swept the marked predicate's
   ;; extent to the instance budget, and a run at 32768 does not finish in 15 minutes.
   {:name      :tuple-mark-determinant-write
    :group     :tuples
    :claim     "32x the tuples under a last-position functionalInArg mark costs under 2x per tuple arriving on a determinant of its own"
    :sizes     [1024 32768]
    :max-ratio 2.0
    :run       tuple-mark-determinant-write}

   ;; `vantage-unrelated-write`, `whole-beside-loser-consequences`,
   ;; `vantage-dissolving-write`, `dissolving-beside-loser-consequences`,
   ;; `vantage-context-edge-unreached`, `context-edge-making-nogoods-whole`,
   ;; `read-below-vantage` and `hidden-check-beside-excepts` hold the cost of a write, a
   ;; read and a belief-status beside the nogoods a vantage decides.  Each bound is the file's flat-claim 2.0x, or twice
   ;; the size ratio for the claim per nogood, and no defective implementation has been
   ;; measured against any of them.  Readings of 2026-10-04 under `--only`, load 5 to 9.
   ;;
   ;; Measured 0.89x and 1.03x (0.53 ms against 0.54).
   {:name      :vantage-unrelated-write
    :group     :placement
    :claim     "16x the decided nogoods at a vantage costs under 2x per fact naming none of them, asserted and read there"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       vantage-unrelated-write}

   ;; Measured 2026-10-06 under `--only`, load 13 to 40: 9.91x (27.0 ms per write at 64,
   ;; 267.3 at 1024) when the report read every standing defeat's consequences, 1.08x and
   ;; 1.23x reading what the write can move.
   {:name      :genlcx-edge-beside-unreached-defeats
    :group     :placement
    :claim     "16x the decided nogoods costs under 2x per genlCx edge asserted and retracted under a listener whose contexts see none of them"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genlcx-edge-beside-unreached-defeats}

   ;; Measured 2026-10-09 at load 50: 8.04x (0.93 ms/op at 64, 7.44 at 8192) while the
   ;; `genlCx` filter gate built the set of every stored except's and defeat's target, which
   ;; the columnar trie builds per read; 0.84x reading only whether one is stored.
   {:name      :genlcx-edge-beside-seen-excepts-columnar
    :group     :exceptions
    :claim     "128x the excepts its sub already sees costs under 2x per genlCx edge asserted and retracted on memory-columnar"
    :sizes     [64 8192]
    :max-ratio 2.0
    :run       #(binding [*backend* :memory-columnar] (genlcx-edge-beside-seen-excepts %))}

   ;; Measured 2026-10-10 under a probe of this function, load 21 to 32: 5.24x and 6.24x
   ;; (17.7 ms/op at 64, 92.1 and 112.0 at 8192) while the reach (`kb/supporter-reaches?`)
   ;; built the set of every stored except's target at each write; 0.35x and 0.44x
   ;; probing the support's handles.  Building the 32768 excepts took 412 s and 556 s
   ;; against 20 s and 32 s.
   {:name      :excepts-in-one-settle-beside-excepts-columnar
    :group     :exceptions
    :claim     "128x the standing excepts costs under 2x per 16 facts and an except of each asserted under one deferred settle on memory-columnar"
    :sizes     [64 8192]
    :max-ratio 2.0
    :run       #(binding [*backend* :memory-columnar] (excepts-in-one-settle-beside-excepts %))}

   ;; The `genl` gate answers off the `:tax-named` count (`kb/supporter-reaches?`): 0.91x
   ;; at load 23 (1.50 ms/op at 64, 1.36 at 8192), where a build of every stored except's
   ;; and defeat's target per write read 2.35x at load 8 (1.01 and 2.38).
   {:name      :genl-defeat-beside-defeats-columnar
    :group     :placement
    :claim     "128x the standing defeats of other genl edges costs under 2x per genl edge's defeat and a membership read through it on memory-columnar"
    :sizes     [64 8192]
    :max-ratio 2.0
    :run       #(binding [*backend* :memory-columnar] (genl-defeat-beside-defeats %))}

   {:name      :genlcx-edge-beside-seen-excepts-under-a-genlcx-except
    :group     :exceptions
    :claim     "16x the excepts a genlCx edge's sub already sees costs under 2x per edge asserted and retracted, beside an except of another genlCx edge"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       #(genlcx-edge-beside-seen-excepts % true)}

   {:name      :listener-write-beside-defeats
    :group     :placement
    :claim     "16x the decided nogoods, each loser with a consequence chain, costs under 2x per fact naming none of them asserted under a listener"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       listener-write-beside-defeats}

   ;; Measured 0.94x, and 1.21x over unary consequences, under `--only`, load 4 to 5.
   {:name      :whole-beside-loser-consequences
    :group     :placement
    :claim     "16x the consequences of a loser costs under 2x per write making its nogood whole: no consequence is swept"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       whole-beside-loser-consequences}

   ;; Measured 1.00x and 0.86x (1.01 ms against 0.87).
   {:name      :vantage-dissolving-write
    :group     :placement
    :claim     "16x the decided nogoods at a vantage costs under 2x per retract of another nogood's winner"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       vantage-dissolving-write}

   ;; A defeat of a `genl` edge moves the change clock, as every write does, and the next
   ;; scoped read asks which relations a defeat reaches over the smaller of the targets
   ;; and the supporters.
   {:name      :genl-defeat-beside-defeats
    :group     :placement
    :claim     "16x the standing defeats of other genl edges costs under 2x per genl edge's defeat and a membership read through it"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genl-defeat-beside-defeats}

   ;; A defeat retires every scoped closure that reads supporter belief (the change
   ;; clock), and each reader read after it walks its own closure once, whose size the
   ;; readers beside it do not change.
   {:name      :defeat-beside-unreached-readers
    :group     :placement
    :claim     "32x the readers below a genl edge's defeat whose closures it does not reach costs under 2x per closure read at twenty of them after the defeat"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       defeat-beside-unreached-readers}

   ;; A justification added to or dropped from a supporter of a `genl` edge, with no label
   ;; moving, moves the change clock, as a defeat move does, and each reader read after it
   ;; walks its own closure once.
   {:name      :justification-beside-unreached-readers
    :group     :placement
    :claim     "32x the readers below a genl edge a defeat hides whose closures it does not reach costs under 2x per closure read through the edge and at twenty of them after a justification joins it"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       justification-beside-unreached-readers}

   ;; A read of a firing whose witness edge is hidden searches backward from its goal for a
   ;; claim on another route (`inherit/goal-reached?`), seeded off the stored claims with
   ;; the goal's other arguments, so the types under the goal that hold none are not walked.
   ;; Measured 0.79x, and 1.00x over a membership, under `--only`, load 4.6 to 4.9.
   {:name      :hidden-route-beside-unclaimed-types
    :group     :inherit
    :claim     "16x the unclaimed types under a hidden route's end costs under 2x per read of the firing"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       hidden-route-beside-unclaimed-types}

   {:name      :hidden-route-beside-untyped-types
    :group     :inherit
    :claim     "16x the types under a hidden membership route's end costs under 2x per read of the firing"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       hidden-route-beside-untyped-types}

   ;; The search meets each membership once per KB state: its matches are read through the
   ;; literal cache and the scoped closure cache, both keyed on the search's reading.
   ;; Measured 1.15x before the nested search and 1.15x after it, under `--only`.
   {:name      :hidden-route-beside-hidden-claims
    :group     :inherit
    :claim     "16x the memberships each under its own hidden edge to a hidden firing's goal costs under 2x per read of the firing"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       hidden-route-beside-hidden-claims}

   ;; The search reads the membership type's scoped ancestor set from the closure cache, so
   ;; only the first read walks the chain.  Measured 0.63x, against 12.43x for a walk per
   ;; read, under `--only`.
   {:name      :second-route-over-a-deep-chain
    :group     :inherit
    :claim     "16x the types on a firing's second route costs under 2x per read of the firing"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       second-route-over-a-deep-chain}

   ;; The retract re-chains no consequence: the network kept the loser IN, so its firings
   ;; stand, and the placed nogoods over it are read off the term index.  Measured 1.02x,
   ;; and 1.01x over unary consequences.
   {:name      :dissolving-beside-loser-consequences
    :group     :placement
    :claim     "16x the consequences of a loser costs under 2x per retract of its nogood's winner"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       dissolving-beside-loser-consequences}

   {:name      :whole-beside-unary-loser-consequences
    :group     :placement
    :claim     "16x the unary consequences of a loser costs under 2x per write making its nogood whole: no consequence is swept"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       whole-beside-unary-loser-consequences}

   {:name      :dissolving-beside-unary-loser-consequences
    :group     :placement
    :claim     "16x the unary consequences of a loser costs under 2x per retract of its nogood's winner"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       dissolving-beside-unary-loser-consequences}

   ;; Measured 0.97x and 0.73x (1.25 ms against 0.92).
   {:name      :vantage-context-edge-unreached
    :group     :placement
    :claim     "16x the decided nogoods at a vantage costs under 2x per genlCx edge reaching none of them"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       vantage-context-edge-unreached}

   {:name      :context-edge-beside-membership-nogoods
    :group     :placement
    :claim     "16x the membership conflicts standing where a genlCx edge gives no context a new view costs under 2x per edge, its upper end stating a genl edge"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       context-edge-beside-membership-nogoods}

   {:name      :membership-beside-held-types
    :group     :membership
    :claim     "16x the memberships a term holds costs under 2x per membership of a type no separation reaches"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       membership-beside-held-types}

   {:name      :separated-membership-beside-held-types
    :group     :membership
    :claim     "16x the memberships a term holds costs under 20x per membership of a type a separation reaches: linear in the term's types at most"
    :sizes     [64 1024]
    :max-ratio 20.0
    :run       separated-membership-beside-held-types}

   {:name      :cover-beside-kept-denials
    :group     :membership
    :claim     "16x the kept terms holding a membership and a denial the cover does not reach costs under 2x per covering declaration asserted and retracted"
    :sizes     [1000 16000]
    :max-ratio 2.0
    :run       cover-beside-kept-denials}

   {:name      :separation-beside-kept-terms
    :group     :membership
    :claim     "16x the kept terms holding no type under either side costs under 2x per separation declaration asserted and retracted"
    :sizes     [512 8192]
    :max-ratio 2.0
    :run       separation-beside-kept-terms}

   ;; Measured 1.77x and 1.48x (1.59 ms against 2.35): the cost per nogood is small beside
   ;; the edge's own cost at these sizes.
   {:name      :context-edge-making-nogoods-whole
    :group     :placement
    :claim     "8x the nogoods a genlCx edge makes whole costs under 16x per edge: a bound per nogood"
    :sizes     [16 128]
    :max-ratio 16.0
    :run       context-edge-making-nogoods-whole}

   {:name      :context-edge-beside-placements
    :group     :placement
    :claim     "4x the placements each nogood holds costs under 2x per genlCx edge giving it one more"
    :sizes     [15 60]
    :max-ratio 2.0
    :run       #(context-edge-beside-placements :negation %)}

   ;; The same edge beside the other four families' nogoods (`chain/place-sets!`).
   {:name      :context-edge-beside-membership-placements
    :group     :placement
    :claim     "4x the placements each membership nogood holds costs under 2x per genlCx edge giving it one more"
    :sizes     [15 60]
    :max-ratio 2.0
    :run       #(context-edge-beside-placements :membership %)}

   {:name      :context-edge-beside-related-placements
    :group     :placement
    :claim     "4x the placements each related-types nogood holds costs under 2x per genlCx edge giving it one more"
    :sizes     [15 60]
    :max-ratio 2.0
    :run       #(context-edge-beside-placements :related %)}

   {:name      :context-edge-beside-tuple-placements
    :group     :placement
    :claim     "4x the placements each tuple nogood holds costs under 2x per genlCx edge giving it one more"
    :sizes     [15 60]
    :max-ratio 2.0
    :run       #(context-edge-beside-placements :tuple %)}

   {:name      :context-edge-beside-arity-placements
    :group     :placement
    :claim     "4x the contexts below sixteen inert tuples costs under 2x per genlCx edge adding one more"
    :sizes     [15 60]
    :max-ratio 2.0
    :run       #(context-edge-beside-placements :arity %)}

   ;; Measured 0.85x (0.035 ms a batch of twenty at n=1024).
   {:name      :read-below-vantage
    :group     :placement
    :claim     "16x the decided nogoods outside a handle's support costs under 2x per read of it below their vantage"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       read-below-vantage}

   ;; Measured 1.04x (0.19 ms a batch of twenty at n=1024).
   {:name      :hidden-check-beside-excepts
    :group     :exceptions
    :claim     "16x the excepts and decided nogoods on other targets costs under 2x per belief-status of a handle"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       hidden-check-beside-excepts}

   {:name      :read-beside-unseen-defeats
    :group     :placement
    :claim     "16x the decided nogoods in contexts a reader does not see costs under 2x per read there"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       #(read-below-vantage % 'CxPlSide)}

   {:name      :monotonic-chain-beside-seen-defeats
    :group     :placement
    :claim     "16x the depth of a monotonic derivation costs under 2x per read of it where no except is seen"
    :sizes     [3 48]
    :max-ratio 2.0
    :run       monotonic-chain-beside-seen-defeats}

   {:name      :backward-query-beside-candidates
    :group     :placement
    :claim     "16x the nogood candidates no context places costs under 2x per backward query"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       backward-query-beside-candidates}

   ;; Measured 6.48x (0.558 -> 3.613 ms) with the support walk capped at the stored
   ;; defeat count before the extent read, and 0.98x (0.045 ms) reading the extent first.
   {:name      :default-chain-beside-many-unseen-defeats
    :group     :placement
    :claim     "16x the depth of a default derivation costs under 2x per read of it where none of 1,024 defeats is seen"
    :sizes     [3 48]
    :max-ratio 2.0
    :run       default-chain-beside-many-unseen-defeats}

   ;; Measured 13.16x (0.723 -> 9.512 ms) with the exemption gate read over the whole KB,
   ;; and 0.95x (0.047 ms) with it read at the reader.
   {:name      :default-chain-beside-unseen-contradicts
    :group     :placement
    :claim     "16x the depth of a default derivation costs under 2x per read of it where no placement is seen, beside a sibling exception"
    :sizes     [3 48]
    :max-ratio 2.0
    :run       default-chain-beside-unseen-contradicts}

   {:name      :default-chain-beside-unseen-arity-candidates
    :group     :placement
    :claim     "16x the depth of a default derivation costs under 2x per read of it where placements are seen and no arity binding is"
    :sizes     [3 48]
    :max-ratio 2.0
    :run       default-chain-beside-unseen-arity-candidates}

   {:name      :monotonic-read-beside-marks
    :group     :placement
    :claim     "16x the permuting marks costs under 2x per read of a monotonic fact where a defeat is seen"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       monotonic-read-beside-marks}])

;; ---- the runner ---------------------------------------------------------

(def ^:private quick-slack
  "How much `--quick` widens each bound.  One attempt over the real pair is noisier
  than the gate's re-measured best-of-two, so the bound gives that noise room — a
  borderline reading passes where the full gate would look twice, and a genuine
  regression still fails."
  1.5)

(defn- run-check
  "Warm one check once (`warm!`), measure it at both sizes and judge the growth.  A check
  over its bound is measured again, on the same warming, and the *better* ratio stands: a
  GC pause or a scheduler hiccup landing in one window is not a regression, and an
  algorithmic one survives being looked at twice.  A baseline (no `:max-ratio`) is
  measured once and not judged, and an `:unmet` check is measured once and an over-bound
  reading reports `:unmet`."
  [{:keys [sizes max-ratio run unmet]} tolerance quick?]
  (let [[small large] sizes
        ;; the small size first, read after exactly the warming the bounds were calibrated
        ;; against; the large reading is warmer by one small run
        attempt (fn [] (let [a (measure run small)
                             b (measure run large)]
                         {:small a :large b :ratio (/ b (max a 1.0))}))]
    (warm! run large)
    (if (nil? max-ratio)
      (assoc (attempt) :sizes [small large] :status :baseline)
      (let [;; quick widens the bound instead of shrinking the pair: one attempt over the
            ;; real sizes is a coarse verdict, where measuring one size twice is six runs
            ;; and no possible failure — a gate that cannot fail is decoration
            bound     (* (double max-ratio) (double tolerance) (if quick? quick-slack 1.0))
            first-try (attempt)
            best      (if (or quick? unmet (<= (:ratio first-try) bound))
                        first-try
                        (min-key :ratio first-try (attempt)))]
        (assoc best
               :bound  bound
               :sizes  [small large]
               :status (cond (< (:small best) noise-floor-ns) :noise
                             (<= (:ratio best) bound)         :pass
                             unmet                            :unmet
                             :else                            :fail))))))

(defn- report [{:keys [name claim unmet]} {:keys [small large ratio bound sizes status]}]
  (let [[s l] sizes]
    (println (format "  %-20s %s" (clojure.core/name name)
                     (case status
                       :pass     (if unmet "PASS — marked :unmet" "PASS")
                       :fail     "FAIL"
                       :unmet    "UNMET — over the bound, marked :unmet, not failed"
                       :noise    "noise — below the gating floor, not judged"
                       :baseline "baseline — measured, not judged")))
    (println (format "    %s" claim))
    (println (format "    n=%-6d %8.3f ms/op        n=%-6d %8.3f ms/op"
                     s (/ small 1e6) l (/ large 1e6)))
    (case status
      :noise    nil
      :baseline (println (format "    growth %.2fx  (no bound)" ratio))
      (println (format "    growth %.2fx  (bound %.2fx)" ratio bound)))
    (println)))

(defn- usage-exit [msg]
  (binding [*out* *err*]
    (println msg)
    (println "usage: lein perf [--only <name|group>[,…]] [--tolerance <x>] [--quick] | --list"))
  (System/exit 2))

(defn- parse-args [args]
  ;; refused, not guessed: `--only` with no value would run the WHOLE gate while
  ;; reading as a single-check run, a dropped unknown flag gates at the default
  ;; tolerance (`--tolerence 1.5` at 1.0), and a bare `--tolerance` NPEs — which
  ;; gate.sh reports exactly like a regression
  (loop [m {:tolerance 1.0 :quick? false :only nil :list? false} [a & more] args]
    (case a
      nil          m
      "--list"     (recur (assoc m :list? true) more)
      "--quick"    (recur (assoc m :quick? true) more)
      "--only"     (let [names (into #{} (comp (map str/trim) (remove str/blank?) (map keyword))
                                     (some-> (first more) (str/split #",")))]
                     (if (seq names)
                       (recur (assoc m :only names) (rest more))
                       (usage-exit "--only needs a check or group name")))
      "--tolerance" (if-some [v (first more)]
                      (let [x (try (Double/parseDouble v)
                                   (catch NumberFormatException _
                                     (usage-exit (str "--tolerance: not a number: " v))))]
                        (recur (assoc m :tolerance x) (rest more)))
                      (usage-exit "--tolerance needs a number"))
      (usage-exit (str "unknown flag: " a)))))

(defn -main [& args]
  (let [{:keys [tolerance quick? only list?]} (parse-args args)
        selected (cond->> checks
                   only (filter #(or (contains? only (:name %)) (contains? only (:group %)))))
        unknown  (sort (remove (into (set (keys groups)) (map :name) checks) only))
        ungroup  (remove #(contains? groups (:group %)) checks)]
    (when (seq ungroup)
      (println "no group in `groups`:" (mapv (juxt :name :group) ungroup))
      (System/exit 2))
    ;; `--list` prints each check's group, name and claim and measures nothing
    (when list?
      (doseq [{:keys [name group claim]} checks]
        (println (format "%-12s %-48s %s" (clojure.core/name group) (clojure.core/name name)
                         claim)))
      (System/exit 0))
    (when (seq unknown)
      (println "no such check or group:" (str/join ", " unknown)
               "— groups:" (vec (keys groups)) "— checks:" (mapv :name checks))
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
          (let [named (fn [st] (into [] (comp (filter (fn [[_ r]] (= st (:status r))))
                                              (map (comp :name first)))
                                     results))
                noisy (named :noise)
                bases (named :baseline)
                unmet (named :unmet)]
            ;; the floor's whole point: a check too fast to gate says so instead of
            ;; turning into a green light nobody notices has stopped meaning anything
            (println (format "%d check(s) ok%s%s%s"
                             (- (count results) (count noisy) (count bases) (count unmet))
                             (if (seq noisy)
                               (format ", %d below the gating floor — not judged: %s"
                                       (count noisy) noisy)
                               "")
                             (if (seq bases)
                               (format ", %d baseline(s) — not judged: %s"
                                       (count bases) bases)
                               "")
                             (if (seq unmet)
                               (format ", %d unmet — over the bound, not failed: %s"
                                       (count unmet) unmet)
                               "")))
            (shutdown-agents)
            (System/exit 0)))))))
