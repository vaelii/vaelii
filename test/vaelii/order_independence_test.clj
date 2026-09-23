;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.order-independence-test
  "The engine-wide invariant: **the same knowledge, given in any order, yields the
  same beliefs.**

  This is not a nice-to-have. A common-sense KB learns generalities and specifics in
  whatever order the world supplies them — 'birds fly' before or after 'Tweety is a
  penguin' — and an engine whose answers depend on that order is answering a
  question nobody asked.

  These tests enumerate *every* permutation of a scenario's assertions and demand a
  single distinct outcome. They are the regression net for the region-local
  relabelling in `vaelii.impl.jtms`: a local fixpoint is only legitimate because it
  agrees with the global one, and disagreement shows up here as an order-dependent
  answer.

  Note what a weaker test would have missed. The Nixon-diamond case once asserted
  only that *exactly one* side won — which is true under every order even when the
  winner flips. It passed while the engine was order-dependent, because the tie-break
  keyed on handle id and handles are allocated in assertion order (see
  `vaelii.impl.solve/content-key`). Demanding the *identical reading* every time is
  what catches that, and it is why `observe` returns a map compared as a whole rather
  than a boolean per ordering.

  The Nixon diamond has no winner to be stable about: two rules concluding `P` and
  `¬P` with neither naming the other's case is a **represented dilemma**, so both
  sides stay believed and the pair is reported by `contradictions`
  (docs/exceptions.md, \"What surfaces where\"). The expected outcome is therefore
  \"both always coexist, and exactly one dilemma is always reported\" rather than
  \"the same one side always wins\". The dilemma count is in
  `observe` deliberately: a report that appeared under some orderings and not others,
  or that double-counted a pair, is precisely the order-dependence this file exists to
  catch, and it would be invisible to a belief-only reading."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(defn- interleavings
  "Every **linear extension** of `chains`: each chain's ops keep their own relative
  order, and the chains interleave with one another freely.  An op that constrains
  nothing is a chain of one, so a flat permutation is the all-singletons case.

  This is what an ordering test containing a **removal** needs and a flat permutation
  cannot express.  A `retract!` names a handle its own assertion allocated, so it may
  not precede it — and tying the pair into a single op would remove the very window
  such a test is about, the third op arriving *between* them.  Stated as a chain, the
  constraint is declared once and every legal ordering follows from it.

  The count is the multinomial: chains of 3, 1 and 1 give 5!/3!1!1! = 20."
  [chains]
  (let [chains (into [] (remove empty?) chains)]
    (if (empty? chains)
      (list ())
      (for [i    (range (count chains))
            tail (interleavings (update chains i rest))]
        (cons (first (nth chains i)) tail)))))

(defn- permutations
  "Every ordering of `coll` — the `interleavings` of ops that constrain one another not
  at all."
  [coll]
  (interleavings (mapv vector coll)))

;; How many orderings the *sampled* order-independence check walks when running the
;; full n! every time is too dear.  Order-independence is enforced here as a
;; regression net, not proven: a deterministic spread of orderings catches a
;; region-local relabelling that went order-sensitive without paying for the whole
;; cross-product.  Almost every scenario below runs an ordering in ~1 ms and so walks
;; all of them (no cap).  The cap is for the scenarios too dear to walk whole every
;; time: the derived-edge tests at the end, whose every ordering recomputes the genlCx
;; closure and costs ~2 s, and the permuting-mark tests, whose 720 orderings cost 2-4 s
;; and which keep a ^:slow twin walking all of them.  Raise this — or drop the cap at
;; the call site — for an exhaustive audit.
(def ^:private ordering-sample 16)

(defn- shuffle-seeded
  "A reproducible shuffle: same seed, same order, independent of run.  Test code, so
  `java.util.Random` with a fixed seed rather than `clojure.core/shuffle`'s
  run-varying one — a sampled failure has to reproduce."
  [seed coll]
  (let [al (java.util.ArrayList. ^java.util.Collection coll)]
    (java.util.Collections/shuffle al (java.util.Random. (long seed)))
    (vec al)))

(defn- sampled-orderings
  "A deterministic sample of up to `n` of `orderings`: always the two extremes a
  relabelling is likeliest to split on, which `interleavings` returns first and last —
  the ops in the order they were given and in the reverse of it, each chain's own order
  intact — then a fixed-seed spread of the rest.  Returns them all unchanged when there
  are `n` or fewer."
  [n orderings]
  (let [v (vec orderings)]
    (if (<= (count v) n)
      v
      (into [(first v) (peek v)]
            (take (- n 2) (shuffle-seeded 42 (subvec v 1 (dec (count v)))))))))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (list 'implies (cons 'and antes) conseq))))

(defn- run-ops
  "Apply `ops` to a freshly cleared KB and return `observe`'s reading of it."
  [ops observe]
  (let [kb (tu/fresh)]
    (doseq [op ops] (op kb))
    (observe kb)))

(defn- outcome-census
  "The distinct outcomes over `orderings`, each mapped to how many produced it (`:n`) and
  the index of the first that did (`:at`) — the form a failure is read from.  A
  sixteen-against-four split says at once which side is the defect, where a bare set of
  readings leaves that to be guessed, and the index reproduces it: `interleavings` is
  deterministic, so ordering #3 is the same ordering on the next run."
  [orderings observe]
  (reduce (fn [acc [i o]]
            (if (contains? acc o)
              (update-in acc [o :n] inc)
              (assoc acc o {:n 1 :at i})))
          {}
          (map-indexed (fn [i ops] [i (run-ops ops observe)]) orderings)))

(def ^:private census-lines
  "How many outcomes a failure prints in full.  A split is nearly always two-way and a
  reader wants both; the cap is for the pathological case — an `observe` accidentally
  reading something arrival-ordered makes every ordering its own outcome, and dozens of
  whole-KB readings printed in full bury the count that says what went wrong."
  6)

(defn- census-report
  "A census as failure text, one line per outcome, earliest first."
  [census]
  (let [ranked (sort-by (comp :at val) census)]
    (str (apply str (for [[o {:keys [n at]}] (take census-lines ranked)]
                      (str "\n  " n "x (first at #" at ") " (pr-str o))))
         (when (> (count ranked) census-lines)
           (str "\n  ... and " (- (count ranked) census-lines) " more outcome(s)")))))

(defn- outcomes
  "The set of distinct outcomes over the given `orderings`."
  [orderings observe]
  (set (keys (outcome-census orderings observe))))

(defn- one-outcome-under!
  "Assert that every linear extension of `chains` agrees, and return the single outcome.

  The general form: `one-outcome!` is this with every op its own chain.  Reach for this
  one whenever an op depends on an earlier one — a `retract!` on the handle an `assert`
  allocated, an un-merge on the merge it lifts — where a flat permutation would produce
  orderings that cannot be run at all.  `cap` samples, exactly as `one-outcome!` does."
  ([label chains observe] (one-outcome-under! label chains observe nil))
  ([label chains observe cap]
   (let [all    (interleavings chains)
         walked (cond->> all cap (sampled-orderings cap))
         census (outcome-census walked observe)]
     (is (= 1 (count census))
         (str label ": " (count census) " distinct outcomes across " (count walked)
              (when cap (str " sampled of " (count all))) " orderings —"
              (census-report census)))
     (key (first (sort-by (comp :at val) census))))))

(defn- one-outcome!
  "Assert that every ordering of `ops` agrees, and return the single outcome.  With a
  `cap`, walk a deterministic sample of that many orderings instead of the full n! —
  for a scenario whose per-ordering cost makes the exhaustive walk too dear to run
  every time (see `ordering-sample`).  Ops that constrain one another cannot be stated
  here; they belong in `one-outcome-under!`."
  ([label ops observe] (one-outcome! label ops observe nil))
  ([label ops observe cap]
   (one-outcome-under! label (mapv vector ops) observe cap)))

(defn- one-outcome-necessarily!
  "Assert order-independence over `ops`, as `one-outcome!` does, and additionally that
  every op is necessary: removing any single one gives a reading different from the whole.
  Return the single outcome.

  `one-outcome!` proves the N ops are *sufficient* for the reading and that no ordering of
  them changes it.  It does not prove the reading needs all N.  An op that moves no field
  of the reading — a taxonomy edge the conclusion is reached without, a fact the outcome
  never mentions — passes `one-outcome!`, and a KB that never received that op reads the
  same, so the scenario does not test the op's presence at all.  This runs each N-1 subset
  (the ops in their given order, one dropped) and fails naming any op whose removal
  reproduces the outcome.

  The reading is what decides necessity, so a reproduced outcome is a reason to enrich the
  `observe` before it is a reason to drop the op: a field that separates the op's own
  mechanism from an outcome reached another way makes the op necessary and the test
  stronger.  Flat ops only — ops that constrain one another, a `retract!` on the handle its
  own `assert` allocated, cannot drop independently and belong with the confluence tests
  below.

  The necessity leg drops each op from its given-order position and runs that N-1 subset
  once, so a *pass* is conclusive (a globally-redundant op reproduces the outcome in the
  given order too, and is caught) but a *redundant verdict* is given-order-only: an op the
  check flags could still be necessary under some other order, if the N-1 subset is itself
  order-dependent.  So a flag is a reason to enrich or to confirm all-order inertness
  before trimming the op, never on its own a licence to drop it."
  ([label ops observe] (one-outcome-necessarily! label ops observe nil))
  ([label ops observe cap]
   (let [ops       (vec ops)
         outcome   (one-outcome! label ops observe cap)
         redundant (into []
                         (keep (fn [i]
                                 (when (= outcome
                                          (run-ops (into (subvec ops 0 i)
                                                         (subvec ops (inc i)))
                                                   observe))
                                   i)))
                         (range (count ops)))]
     (is (empty? redundant)
         (str label ": every op must be necessary, but removing op(s) " (pr-str redundant)
              " left the reading unchanged — a KB that never received them reads it too, so"
              " the scenario does not test their presence.\n  outcome: " (pr-str outcome)))
     outcome)))

;; ---- defaults and their exceptions --------------------------------------

(deftest penguin-cascade-is-order-independent
  ;; 5 assertions, 120 orderings. The default may fire before or after the KB learns
  ;; Tweety is a penguin, before or after it learns penguins are birds at all.
  ;;
  ;; `one-outcome-necessarily!`, so every one of the five is required for the reading and
  ;; not only agreed upon by the orderings.  The `:tweety-is-bird` field is why
  ;; `(genl penguin bird)` is among them: without it Tweety is not a bird, the flight
  ;; default never applies, and `(flies Tweety)` is absent for that reason instead of the
  ;; intended one — an outcome a `:tweety-flies` reading alone cannot tell from the
  ;; exception defeating the default, so the edge would drop with the reading unchanged.
  ;; With the inherited membership in the reading, the edge moves it and is necessary.
  (let [ops [#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)
             #(v/assert-rule % '[(penguin ?x)] '(not (flies ?x)) 'CxUniverse {:direction :forward})
             #(v/assert % '(genl penguin bird) 'CxUniverse)
             ;; Known-true: a bare rule confers :monotonic and is capped by its weakest
             ;; antecedent, so over this premise the exception concludes :monotonic and
             ;; out-ranks the :default flight rule.  Over a :default premise both sides
             ;; would tie at :default and the pair would be a represented dilemma.
             #(v/assert % '(penguin Tweety) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(bird Robin) 'CxUniverse)]
        observe (fn [kb]
                  {:tweety-flies (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'CxUniverse)))
                   :tweety-grounded (boolean (seq (v/sentexes-matching kb '(not (flies Tweety)) 'CxUniverse)))
                   :tweety-is-bird (v/isa? kb 'Tweety 'bird)
                   :robin-flies (boolean (seq (v/sentexes-matching kb '(flies Robin) 'CxUniverse)))
                   :conflicts (count (v/conflicts kb))})
        result (one-outcome-necessarily! "penguin cascade" ops observe)]
    (testing "and the one outcome is the common-sense one"
      (is (false? (:tweety-flies result)))
      (is (true? (:tweety-grounded result)))
      (is (true? (:tweety-is-bird result)))             ; the edge places the penguin under bird
      (is (true? (:robin-flies result)))                ; the exception is not contagious
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest exceptwhen-is-order-independent
  ;; The exception is a belief-following meta-sentex split off from the rule, so the
  ;; exceptWhen may arrive before its facts (blocking the firing at derive time) or
  ;; after them (sweeping a conclusion that already fired).  Both must settle to the
  ;; same belief, forward *and* backward — the whole point of the block/sweep machinery
  ;; being order-independent.  24 orderings.
  ;;
  ;; The `:tweety-is-bird` field is why `(bird Tweety)` is necessary: without it Tweety is
  ;; not a bird, the rule never applies, and `(flies Tweety)` is absent for that reason
  ;; instead of the exception blocking it — an outcome a flight-only reading cannot tell
  ;; from the block, so the fact would drop with the reading unchanged.
  (let [ops [#(v/assert % '(exceptWhen (penguin ?x)
                                       (set/defaultRule (set/forwardRule (implies (and (bird ?x)) (flies ?x)))))
                        'CxUniverse {:direction :forward})
             #(v/assert % '(penguin Tweety) 'CxUniverse)
             #(v/assert % '(bird Tweety) 'CxUniverse)
             #(v/assert % '(bird Robin) 'CxUniverse)]
        observe (fn [kb]
                  {:tweety-query (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'CxUniverse)))
                   :tweety-ask   (v/ask? kb '(flies Tweety) 'CxUniverse)
                   :tweety-is-bird (v/isa? kb 'Tweety 'bird)
                   :robin-query  (boolean (seq (v/sentexes-matching kb '(flies Robin) 'CxUniverse)))
                   :conflicts    (count (v/conflicts kb))})
        result (one-outcome-necessarily! "exceptWhen" ops observe)]
    (testing "the excepted binding never flies, forward or backward; the other does"
      (is (false? (:tweety-query result)))
      (is (false? (:tweety-ask result)))
      (is (true? (:tweety-is-bird result)))             ; the blocked rule's premise stands
      (is (true? (:robin-query result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest two-independent-exceptions-are-order-independent
  ;; Two exceptWhens on the *same* rule (block-if-either), asserted separately, amend
  ;; the one rule.  Every ordering of the two exceptions, the two triggers, and the
  ;; plain fact must ground each excepted bird and let the plain one fly.  6 items would
  ;; be 720 orderings; a diverse handful pins the interesting ones (exceptions before
  ;; and after their triggers, interleaved) without the runtime.
  (doseq [order [[:r1 :r2 :fp :tp :fo :to :fr]
                 [:fp :fo :fr :tp :to :r1 :r2]
                 [:r1 :fp :tp :r2 :fo :to :fr]
                 [:fr :tp :r2 :fo :fp :r1 :to]
                 [:tp :to :fr :fp :fo :r2 :r1]]]
    (let [kb (tu/fresh)
          op {:r1 #(v/assert kb '(exceptWhen (penguin ?x)
                                             (set/defaultRule (set/forwardRule (implies (and (bird ?x)) (flies ?x)))))
                             'CxUniverse)
              :r2 #(v/assert kb '(exceptWhen (ostrich ?x)
                                             (set/defaultRule (set/forwardRule (implies (and (bird ?x)) (flies ?x)))))
                             'CxUniverse)
              :fp #(v/assert kb '(bird Pengu) 'CxUniverse)
              :tp #(v/assert kb '(penguin Pengu) 'CxUniverse)
              :fo #(v/assert kb '(bird Ostri) 'CxUniverse)
              :to #(v/assert kb '(ostrich Ostri) 'CxUniverse)
              :fr #(v/assert kb '(bird Robby) 'CxUniverse)}]
      (doseq [k order] ((op k)))
      (is (empty? (v/sentexes-matching kb '(flies Pengu) 'CxUniverse)) (str order " penguin flies"))
      (is (empty? (v/sentexes-matching kb '(flies Ostri) 'CxUniverse)) (str order " ostrich flies"))
      (is (seq (v/sentexes-matching kb '(flies Robby) 'CxUniverse)) (str order " robin grounded"))
      (tu/clear-kb! kb))))

(deftest a-default-feeding-a-bare-rule-is-order-independent
  ;; The downstream conclusion (can_travel) must track the defeat of its antecedent
  ;; whichever order the pieces arrive in.
  ;;
  ;; Robin is a plain bird with no exception, so the default flies it and the travel rule
  ;; carries it: the positive control that makes the default (op 0) and the travel rule
  ;; (op 1) necessary, and the one place `can_travel`'s forward direction is exercised in
  ;; this file.  `:tweety-is-bird` makes `(genl penguin bird)` necessary for the same reason
  ;; as `penguin-cascade` — without it Tweety is grounded for not being a bird rather than
  ;; for the exception defeating the default.  With Robin and that field every op is
  ;; necessary, so this runs under `one-outcome-necessarily!`.  6 assertions, 720 orderings.
  (let [ops [#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)
             #(v/assert-rule % '[(flies ?x)] '(can_travel ?x) 'CxUniverse {:direction :forward})
             #(v/assert-rule % '[(penguin ?x)] '(not (flies ?x)) 'CxUniverse {:direction :forward})
             #(v/assert % '(genl penguin bird) 'CxUniverse)
             ;; known-true, so the exception concludes :monotonic and defeats the default
             #(v/assert % '(penguin Tweety) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(bird Robin) 'CxUniverse)]
        observe (fn [kb]
                  {:flies (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'CxUniverse)))
                   :travels (boolean (seq (v/sentexes-matching kb '(can_travel Tweety) 'CxUniverse)))
                   :tweety-is-bird (v/isa? kb 'Tweety 'bird)
                   :robin-flies (boolean (seq (v/sentexes-matching kb '(flies Robin) 'CxUniverse)))
                   :robin-travels (boolean (seq (v/sentexes-matching kb '(can_travel Robin) 'CxUniverse)))})
        result (one-outcome-necessarily! "default feeding a bare rule" ops observe)]
    (testing "a defeated antecedent withdraws the conclusion built on it"
      (is (false? (:flies result)))
      (is (false? (:travels result))))
    (testing "while the plain bird flies and travels — the rules do fire when nothing defeats them"
      (is (true? (:tweety-is-bird result)))
      (is (true? (:robin-flies result)))
      (is (true? (:robin-travels result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-rule-joined-to-a-growing-transitive-extent-is-order-independent
  ;; The closure of a user-declared `transitive` predicate is answered by a PROVER and
  ;; never stored, so no pair of it is ever a datum on the agenda.  A rule joined to it
  ;; can therefore only reach a closure pair from its *other* antecedent's trigger — and
  ;; when a later link extends the closure, nothing puts that trigger back.
  ;;
  ;;   (does A1 E0)  (causes E0 E1)  (causes E1 E2)  (does A0 E1)
  ;;
  ;; `(responsibleFor A1 E2)` needs `(does A1 E0)` joined to the closure pair
  ;; `(causes E0 E2)`, which exists only once BOTH links are in.  Assert the `does`
  ;; first and the trigger has already fired against a shorter closure; assert it last
  ;; and the join reaches the whole of it.
  ;;
  ;; This is the exact office `special/subsumption-seeds` does for a `genl` edge, whose
  ;; docstring states the principle: "firing the rules keyed on `genl` is not the same
  ;; thing as re-firing the rules the edge just connected".  `special/transitive-seeds`
  ;; is that for a transitive link.  Two `does` facts rather than one because a single
  ;; one is reached by the surviving trigger in every order and the split does not show.
  (let [ops [#(v/assert % '(does A1 E0) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(does A0 E1) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(causes E0 E1) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(causes E1 E2) 'CxUniverse {:strength :monotonic})]
        observe (fn [kb]
                  {:responsible (set (map :sentence
                                          (v/sentexes-matching kb '(responsibleFor ?a ?e)
                                                               'CxUniverse)))})
        result (one-outcome-under!
                "a rule joined to a growing transitive extent"
                (into [[#(v/assert % '(transitive causes) 'CxUniverse {:strength :monotonic})
                        #(v/assert-rule % '[(does ?a ?act) (causes ?act ?e)]
                                        '(responsibleFor ?a ?e) 'CxUniverse {:direction :forward})]]
                      (mapv vector ops))
                observe
                ordering-sample)]
    (testing "the agent reaches every event its action causes, however the links arrived"
      (is (= '#{(responsibleFor A1 E1)
                (responsibleFor A1 E2)
                (responsibleFor A0 E2)}
             (:responsible result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-rule-over-a-growing-prover-extent-is-order-independent
  ;; The antecedent `(causes ?act ?e)` is answered by the TRANSITIVITY prover, so its
  ;; extent grows as each link of the chain arrives — and a rule whose join is driven
  ;; from the other side sees only the extent that existed when it last fired.  Four
  ;; assertions, 24 orderings, and the outcome must be the three conclusions the closure
  ;; supports whichever order the links arrive in.
  ;;
  ;; The long-chain half of the pair.  What re-drives the join as the closure grows is
  ;; `special/transitive-seeds` (docs/inference.md); the sibling below,
  ;; `a-rule-joined-to-a-growing-transitive-extent-…`, is the two-agent shape that
  ;; isolated the defect, and this one walks a three-link chain instead.  Both ran
  ;; order-dependent before the seeding and neither needs the cost ranking pinned to
  ;; hold, which is the point: completeness here is the chainer's, not the estimator's.
  (let [ops [#(v/assert % '(transitive causes) 'CxUniverse {:strength :monotonic})
             #(v/assert-rule % '[(does ?a ?act) (causes ?act ?e)]
                             '(responsibleFor ?a ?e) 'CxUniverse {:direction :forward})
             #(v/assert % '(does FoxO Flatter) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(causes Flatter Sings) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(causes Sings Falls) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(causes Falls GetsCheese) 'CxUniverse {:strength :monotonic})]
        observe (fn [kb]
                  {:responsible (set (map :sentence
                                          (v/sentexes-matching kb '(responsibleFor ?a ?e)
                                                               'CxUniverse)))})
        ;; 720 orderings, sampled: the split this guards against is a majority of them,
        ;; so a deterministic spread finds it at a fraction of the walk (`ordering-sample`
        ;; above says why sampling is the norm here).
        result (one-outcome-necessarily! "a rule over a growing prover extent" ops observe 120)]
    (testing "every link of the causal chain is one the agent is responsible for"
      (is (= '#{(responsibleFor FoxO Sings)
                (responsibleFor FoxO Falls)
                (responsibleFor FoxO GetsCheese)}
             (:responsible result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-re-assert-never-downgrades-a-premises-class
  ;; The class a sentex is held at is resolved from **content**, so the entry point cannot let
  ;; arrival order decide it.  A re-assert carrying no `:strength` states nothing about
  ;; the class — the `:default` it falls back to is the entry point's fallback, not the
  ;; caller's claim — so reading that silence as a downgrade retired the known-true
  ;; mark: asserted monotonic, re-asserted bare, and then met by a known-true negation,
  ;; the original was *defeated*, where the same three sentences without the bare
  ;; re-assert left an irreducible pair.  Six orderings, one outcome.
  ;;
  ;; `one-outcome!`, not `one-outcome-necessarily!`: this test's claim is that the bare
  ;; re-assert (op 1) changes nothing, so it is deliberately not necessary and a
  ;; leave-one-out check would forbid the very no-op under test.  The narrowing that a
  ;; re-assert cannot do is checked by the retract-and-re-assert block below.
  (let [ops [#(v/assert % '(flies Tweety) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(flies Tweety) 'CxUniverse)
             #(v/assert % '(not (flies Tweety)) 'CxUniverse {:strength :monotonic})]
        observe (fn [kb]
                  (let [pos (v/handle-of kb '(flies Tweety) 'CxUniverse)
                        neg (v/handle-of kb '(not (flies Tweety)) 'CxUniverse)]
                    {:flies       (v/in? kb pos)
                     :not-flies   (v/in? kb neg)
                     :flies-class (v/defeat-class kb pos)
                     :conflicts   (count (v/conflicts kb))}))
        result (one-outcome! "a bare re-assert of monotonic content" ops observe)]
    (testing "the bare re-assert leaves the known-true mark where it found it"
      (is (= :monotonic (:flies-class result))))
    (testing "so the pair is the irreducible clash it is without the re-assert"
      (is (true? (:flies result)))
      (is (true? (:not-flies result)))
      (is (= 1 (:conflicts result))))
    (testing "and narrowing a class is still retract! and re-assert"
      (let [kb (tu/fresh)
            h  (v/assert kb '(flies Tweety) 'CxUniverse {:strength :monotonic})]
        (v/retract! kb h)
        (is (= :default (v/defeat-class kb (v/assert kb '(flies Tweety) 'CxUniverse)))
            "a retraction takes the class with it, leaving none to inherit")))
    (tu/clear-kb! (tu/test-kb))))

;; ---- a block condition asked over a merged term -------------------------

(defn- blocked-observe
  "The reading a block-condition scenario is judged by: every conclusion the KB holds on
  `seen`, the backward entry point's answer for each of `subjects`, whether the scenario's
  `merge-pair` did merge, and the clash report.  The stored sentences alone would not
  separate a conclusion that was never drawn from one drawn and then swept under a name
  nobody asks about, and `:merged` is why a scenario named for a merged term does not pass
  with the merge a no-op."
  [seen subjects merge-pair]
  (fn [kb]
    {:seen      (set (map :sentence (v/sentexes-matching kb (list seen '?x) '?c)))
     :asked     (mapv #(v/ask? kb (list seen %) 'CxUniverse) subjects)
     :merged    (apply v/same-class? kb merge-pair)
     :conflicts (count (v/conflicts kb))}))

(deftest a-block-condition-over-a-merged-term-is-order-independent
  ;; A block condition is decided three times over — at derive time from the firing's
  ;; raw bindings, again from a trigger, and again off a refusal record — and a merge
  ;; can retire the spelling either the *binding* or the *conjunct's own constant* is
  ;; written in.  A goal asked under a retired spelling comes back honestly empty, and
  ;; an empty block condition reads as **not excepted**, so the same four sentences
  ;; believed the conclusion or not depending on where the merge landed: 6 of these 24
  ;; orderings for a retired binding, 12 of 24 for a retired conjunct constant.
  ;;
  ;; `except_recheck_test/every-arrival-order-of-a-merge-reaches-one-belief` walks the
  ;; same two shapes over the stored sentences; this reads the backward entry point and the
  ;; clash report beside them, which is what a stored-sentence reading cannot see.
  ;;
  ;; `one-outcome!`, not `one-outcome-necessarily!`: the `:merged` field pins the merge, so
  ;; the merge and the skip are each necessary, but the rule and the mark stay redundant for
  ;; the blocked absence — dropping either leaves `:seen` empty — so a leave-one-out check
  ;; cannot hold.  The block's positive necessity, the same subject seen *without* the skip,
  ;; is the sibling `except_recheck_test`.
  (testing "the firing's own binding is the retired spelling"
    ;; `(qmark QOne)` binds `?x` to a term the merge retires, and the exception has to be
    ;; asked under the representative wherever in the order the merge lands.
    (let [ops [#(v/assert % '(exceptWhen (qskip ?x)
                                         (set/defaultRule (set/forwardRule (implies (and (qmark ?x)) (qseen ?x)))))
                          'CxUniverse {:direction :forward})
               #(v/assert % '(qmark QOne) 'CxUniverse)
               #(v/assert % '(rewriteOf QTwo QOne) 'CxUniverse)
               #(v/assert % '(qskip QOne) 'CxUniverse)]
          result (one-outcome! "a merged binding" ops
                               (blocked-observe 'qseen '[QOne QTwo] '[QOne QTwo]))]
      (is (= {:seen #{} :asked [false false] :merged true :conflicts 0} result)
          "the excepted binding concludes nothing under either spelling, forward or backward")))
  (testing "the exception conjunct's own constant is the retired spelling"
    ;; Nothing the firing binds has merged: what moved is a term the *rule* was written
    ;; with, and an individual-only rewrite holds a rule back from migration, so the
    ;; stored condition keeps naming `COne` for good.
    (let [ops [#(v/assert % '(exceptWhen (cskip COne)
                                         (set/defaultRule (set/forwardRule (implies (and (cmark ?x)) (cseen ?x)))))
                          'CxUniverse {:direction :forward})
               #(v/assert % '(cmark CBase) 'CxUniverse)
               #(v/assert % '(rewriteOf CTwo COne) 'CxUniverse)
               #(v/assert % '(cskip CTwo) 'CxUniverse)]
          result (one-outcome! "a merged conjunct constant" ops
                               (blocked-observe 'cseen '[CBase] '[COne CTwo]))]
      (is (= {:seen #{} :asked [false] :merged true :conflicts 0} result)
          "a conjunct naming a retired term is asked under the representative that answers")))
  (tu/clear-kb! (tu/test-kb)))

(deftest naf-over-a-merged-term-is-order-independent
  ;; The same root cause in the polarity where the wrong answer is **unsound**.  An
  ;; `(unknown S)` inner query asked under a retired spelling is answered *absent* about a
  ;; term the KB has an answer for under its representative, so the rule concludes where
  ;; it must not — where a silently-false exception merely fails to guard.  This one did
  ;; not vary with the ordering at all: it drew the conclusion in all 24.
  ;;
  ;; `one-outcome!`, not `one-outcome-necessarily!`: the `:merged` field pins the merge, so
  ;; the merge and the `nskip` fact are each necessary, but the rule and the `nmark` fact
  ;; stay redundant for the sound absence — dropping either keeps it absent — so a
  ;; leave-one-out check cannot hold.  The check that the rule fires when it soundly may is
  ;; `naf_test`'s own positive case; here the claim is that a merged term does not make it
  ;; fire when it must not.
  (let [ops [#(v/assert % '(set/defaultRule
                            (set/forwardRule (implies (and (nmark ?x) (unknown (nskip ?x))) (nseen ?x))))
                        'CxUniverse {:direction :forward})
             #(v/assert % '(nmark NOne) 'CxUniverse)
             #(v/assert % '(rewriteOf NTwo NOne) 'CxUniverse)
             #(v/assert % '(nskip NOne) 'CxUniverse)]
        result (one-outcome! "naf over a merged term" ops
                             (blocked-observe 'nseen '[NOne NTwo] '[NOne NTwo]))]
    (testing "a term with an answer under its representative is not absent"
      (is (= {:seen #{} :asked [false false] :merged true :conflicts 0} result))))
  (tu/clear-kb! (tu/test-kb)))

;; ---- the represented dilemma --------------------------------------------

(deftest nixon-diamond-is-the-same-dilemma-every-time
  ;; Two equally-specific defaults collide with no strength and no specificity to
  ;; separate them, and neither rule names the other's case. The engine declines to
  ;; decide that: both sides stay believed and the pair is reported by
  ;; `contradictions`. The whole reading must not vary with typing order —
  ;; which sides are believed, that neither was defeated, and that exactly one dilemma
  ;; is reported.
  (let [ops [#(v/assert % (default-rule '[(quaker ?x)] '(pacifist ?x)) 'CxUniverse)
             #(v/assert % (default-rule '[(republican ?x)] '(not (pacifist ?x))) 'CxUniverse)
             #(v/assert % '(quaker Nixon) 'CxUniverse)
             #(v/assert % '(republican Nixon) 'CxUniverse)]
        observe (fn [kb]
                  (let [pos (v/handle-of kb '(pacifist Nixon) 'CxUniverse)
                        neg (v/handle-of kb '(not (pacifist Nixon)) 'CxUniverse)]
                    {:pacifist (boolean (seq (v/sentexes-matching kb '(pacifist Nixon) 'CxUniverse)))
                     :not-pacifist (boolean (seq (v/sentexes-matching kb '(not (pacifist Nixon)) 'CxUniverse)))
                     ;; the defeat-classes, not the handles: handles are allocated in
                     ;; assertion order, so putting one in the reading would make every
                     ;; ordering differ for a reason that is not about belief.  Keyed
                     ;; positive-then-negative, so a defeated or missing side reads as
                     ;; nil in its own slot rather than vanishing into a set.
                     :classes [(v/defeat-class kb pos) (v/defeat-class kb neg)]
                     :contradictions (count (v/contradictions kb))
                     :conflicts (count (v/conflicts kb))}))
        result (one-outcome-necessarily! "nixon diamond" ops observe)]
    (testing "both sides are believed — the dilemma is represented, not decided"
      (is (true? (:pacifist result)))
      (is (true? (:not-pacifist result))))
    (testing "and neither was defeated — both still stand at :default"
      (is (= [:default :default] (:classes result))))
    (testing "the pair is reported once as a dilemma, not as a conflict"
      (is (= 1 (:contradictions result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest the-reported-lists-are-content-ordered-not-arrival-ordered
  ;; The count being stable is not enough, and the two tests above only check counts.
  ;; `settle` stores both readings in arrival order — they come off a hash set of
  ;; handle-keyed nogoods — and `settle/ranked`, called by `conflicts` and by
  ;; `contradictions`, is the whole of what makes the *list* an answer about the
  ;; knowledge.  A reader that stops calling it puts `(first (contradictions kb))` at
  ;; the mercy of which pair was typed first, which no count would notice.  So these
  ;; observe the sequence, not its length.
  ;;
  ;; `clash_oracle_test/the-contradictions-list-is-ordered-by-content-not-arrival` makes
  ;; the same claim for `contradictions` over two hand-written orders; this one covers
  ;; `conflicts` as well and takes every ordering rather than two.
  ;;
  ;; **Three readers call `ranked`, so three arms.**  `preview`'s `:contradictions` is the
  ;; third and the one a count could never catch: its own test reads the field through a
  ;; `set`, which is order-blind on purpose, so dropping the call there would have failed
  ;; nothing.
  ;;
  ;; Three independent pairs, one op each: the pairs share no term, so nothing but the
  ;; ordering rule decides which report leads.  Six orderings.
  (let [pair    (fn [p strength]
                  #(do (v/assert % (list p 'OrderedSubject) 'CxUniverse strength)
                       (v/assert % (list 'not (list p 'OrderedSubject))
                                 'CxUniverse strength)))
        ;; the sort key is each side's sentence, so the predicate name is what orders
        ;; one report against another — named so that content order and any arrival
        ;; order are different questions
        preds   '[ord_gamma ord_alpha ord_beta]
        reading (fn [reports]
                  (mapv #(-> % :sides first :sentence pr-str) reports))]
    (testing "contradictions — three represented dilemmas at :default"
      (let [result (one-outcome-necessarily! "dilemma list ordering"
                                             (mapv #(pair % {}) preds)
                                             (fn [kb] {:order (reading (v/contradictions kb))}))]
        (is (= 3 (count (:order result))) "all three pairs are reported")
        (is (= (sort (:order result)) (:order result))
            "the list is in content order, so no ordering can put a different one first")))
    (testing "conflicts — the same claim for the irreducible :monotonic reading"
      (let [result (one-outcome-necessarily! "conflict list ordering"
                                             (mapv #(pair % {:strength :monotonic}) preds)
                                             (fn [kb] {:order (reading (v/conflicts kb))}))]
        (is (= 3 (count (:order result))) "all three pairs are reported")
        (is (= (sort (:order result)) (:order result))
            "the list is in content order, so no ordering can put a different one first")))
    (testing "preview — the dilemmas a batch would open, read the same way"
      ;; Here the KB carries only the positives, in every order, and one fixed batch
      ;; opens all three dilemmas at once.  So the batch cannot be what varies: what
      ;; varies is the arrival order of the facts the reports are built from, which is
      ;; exactly what the stored vector is in and exactly what `ranked` has to remove.
      (let [result (one-outcome-necessarily!
                    "preview dilemma list ordering"
                    (mapv (fn [p] #(v/assert % (list p 'OrderedSubject) 'CxUniverse {}))
                          preds)
                    (fn [kb]
                      {:order (reading
                               (:contradictions
                                (v/preview kb {:add (mapv (fn [p]
                                                            [(list 'not (list p 'OrderedSubject))
                                                             'CxUniverse {}])
                                                          preds)})))}))]
        (is (= 3 (count (:order result))) "the batch opens all three")
        (is (= (sort (:order result)) (:order result))
            "the previewed list is in content order too, and by the same call")))
    (tu/clear-kb! (tu/test-kb))))

;; ---- a declaration that arrives after the content it convicts -----------
;;
;; A constraint declaration is an ingredient of the clash exactly as the two facts are,
;; so all three orderings of "declaration, fact, fact" are the same knowledge and the KB
;; owes them the same answer.  The engine has two entry points for that answer and the arrival
;; order picks which: a fact written *after* the declaration is refused at the entry point (or
;; weighed into `contradictions` where the opposing claim is defeasible), and a
;; declaration written after the facts is reported by the settle's exposure pass, with
;; belief untouched.  Both declarations take the second entry point by the same route: a
;; declaration in the settle's moved region says what it puts back in question, and the
;; pass sweeps that.
;;
;; **So what a single outcome means here is that the clash is *accounted for*, not that
;; every ordering picks the same entry point.** Which entry point is the constraint policy's business
;; (`checks/arbitrating?`), and under `:refuse` the two answers are deliberately
;; different things: a refusal turns a write away, a report leaves belief alone and names
;; what it found.  What may not vary is whether the KB says anything at all — and the
;; failure these tests are the net for is silence: a mark arriving last, and the pair it
;; forbids standing, believed, and mentioned by nothing.
;;
;; The reading `one-outcome!` compares is therefore the account and the believed extent
;; — never the entry point, which is what the orderings are entitled to differ on.  Two things
;; keep that from being a weakened boolean.  The **count** is compared, not its
;; positivity, so an engine that refused a write *and* reported the pair, or reported one
;; pair twice, fails exactly as one that did neither does.  And every ordering's full
;; reading is kept, so the tests below can go on to check that the entry points actually used
;; are the two that exist and that each ordering used exactly one — a claim about the
;; whole set that no single outcome can carry.
;;
;; At `:default` the extent is identical across every ordering too, so the map there is
;; the strongest reading available: the same beliefs, and one account of the clash in
;; them.

(defn- refusing-assert
  "An `assert` op at `strength` that survives the entry point turning it away, recording the
  refusal in `refusals` instead.  The refusal is one of the two entry points these tests read: a
  KB that refuses the write and a KB that reports the pair have both answered, and one
  that does neither has not."
  [refusals strength sentence]
  (fn [kb]
    (try (v/assert kb sentence 'CxUniverse {:strength strength})
         (catch clojure.lang.ExceptionInfo _ (swap! refusals inc)))))

(defn- constraint-reading
  "How one KB accounted for a definitional clash — per entry point, summed, and the extent the
  account is about.

  `mapv` on the ledger kinds and the extent, `count` everywhere else: every reader here
  is lazy over live state, and this map outlives the KB the ordering walk built it from."
  [kb refusals pattern]
  (let [reported (mapv :violation (v/violations kb))
        weighed  (count (v/contradictions kb))
        stuck    (count (v/conflicts kb))]
    {:refused   refusals
     :reported  reported
     :weighed   weighed
     :stuck     stuck
     :accounted (+ refusals (count reported) weighed stuck)
     :believed  (vec (sort (mapv (comp pr-str :sentence)
                                 (v/sentexes-matching kb pattern 'CxUniverse))))}))

(defn- constraint-outcome!
  "Every ordering of `sentences` at `strength`, as `{:invariant … :readings […]}`.

  `:invariant` is `one-outcome!`'s verdict over the part that may not vary — the account
  and, at `:default`, the extent; `:readings` is every ordering's full reading, for the
  claims about the *set* of entry points used that a single outcome cannot make."
  [label strength sentences pattern]
  (let [refusals (atom 0)
        seen     (atom [])
        ops      (mapv #(refusing-assert refusals strength %) sentences)
        invariant
        (one-outcome!
         label ops
         (fn [kb]
           (let [full (constraint-reading kb @refusals pattern)]
             (reset! refusals 0)
             (swap! seen conj full)
             ;; the extent joins the invariant only where nothing is refused — at
             ;; `:monotonic` the refused write is a fact the KB legitimately does not
             ;; hold, and which fact that is depends on which of the two was written
             ;; first, exactly as two known-true claims about one slot always have
             (cond-> (select-keys full [:accounted])
               (= :default strength) (assoc :believed (:believed full))))))]
    {:invariant invariant :readings @seen}))

(defn- one-entry-point-each!
  "Assert that every ordering used exactly one of the two entry points, and that both entry points are
  used across the set — a scenario where one entry point answers every ordering is one that
  never exercised the other."
  [readings]
  (let [entry-points (mapv (fn [r]
                             (cond-> #{}
                               (pos? (:refused r))        (conj :refused)
                               (seq (:reported r))        (conj :reported)
                               (pos? (:weighed r))        (conj :weighed)
                               (pos? (:stuck r))          (conj :stuck)))
                           readings)]
    (is (every? #(= 1 (count %)) entry-points)
        (str "every ordering answers by exactly one entry point — " (pr-str (frequencies entry-points))))
    (is (< 1 (count (distinct entry-points)))
        (str "and the scenario reaches more than one of them — " (pr-str (frequencies entry-points))))))

(deftest a-late-symmetric-mark-leaves-one-row-for-one-proposition
  ;; `(symmetric P)` is the one mark whose effect is **canonicalization** rather than
  ;; conviction: the entry point sorts a symmetric literal's arguments, so the two spellings of
  ;; one pair store as one sentex.  A mark arriving after both spellings were written
  ;; therefore leaves the KB holding *two* records for one proposition where a KB told the
  ;; same things in the other order holds one — and the retraction of either then withdraws
  ;; half a fact (vaelii#61).  The mark may land anywhere among the facts; what may not
  ;; vary is what the KB stores and believes once it has.
  (let [h   (atom nil)
        ops [[#(reset! h (v/assert % '(bordersOn Spain France) 'CxUniverse))
              #(v/assert % '(bordersOn France Spain) 'CxUniverse)]
             [#(v/assert % '(symmetric bordersOn) 'CxUniverse)]
             [#(v/assert % '(genl bordersOn near) 'CxUniverse)]]
        observe
        (fn [kb]
          {:rows        (count (v/sentexes-matching kb '(bordersOn ?x ?y) 'CxUniverse))
           ;; the two spellings are one proposition, so they are one handle
           :one-handle? (= (v/handle-of kb '(bordersOn Spain France) 'CxUniverse)
                           (v/handle-of kb '(bordersOn France Spain) 'CxUniverse))
           :borders-sf  (v/ask? kb '(bordersOn Spain France) 'CxUniverse)
           :borders-fs  (v/ask? kb '(bordersOn France Spain) 'CxUniverse)
           ;; ...and the derived answers, which is where the second record hid: `near` is
           ;; reached through `(genl bordersOn near)`, so a surviving twin answers both
           :near-sf     (v/ask? kb '(near Spain France) 'CxUniverse)
           :near-fs     (v/ask? kb '(near France Spain) 'CxUniverse)})
        result (one-outcome-under! "late symmetric mark" ops observe)]
    (testing "and the one outcome is the mark-first reading"
      (is (= 1 (:rows result)) "one proposition, one record")
      (is (true? (:one-handle? result)))
      (is (every? true? ((juxt :borders-sf :borders-fs :near-sf :near-fs) result))
          "both spellings hold, and both derived answers with them"))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-symmetric-mark-leaves-nothing-for-a-retraction-to-miss
  ;; The issue's own sequence.  The retraction runs in `observe` rather than as a
  ;; permuted op, because it names the handle the *first* assertion returned and what
  ;; that handle denotes is the whole question: with the mark already in, it is the pair;
  ;; retracted before the mark arrives it is one of two rows, and the KB legitimately
  ;; keeps the other.  So the mark ranges over every position among the facts, the
  ;; retraction stays after all of them, and every ordering must withdraw the proposition
  ;; whole — including the two `near` answers derived through the predicate above it.
  (let [h   (atom nil)
        ops [[#(reset! h (v/assert % '(bordersOn Spain France) 'CxUniverse))
              #(v/assert % '(bordersOn France Spain) 'CxUniverse)]
             [#(v/assert % '(symmetric bordersOn) 'CxUniverse)]
             [#(v/assert % '(genl bordersOn near) 'CxUniverse)]]
        observe
        (fn [kb]
          (v/retract! kb @h)
          {:rows       (count (v/sentexes-matching kb '(bordersOn ?x ?y) 'CxUniverse))
           :borders-sf (v/ask? kb '(bordersOn Spain France) 'CxUniverse)
           :borders-fs (v/ask? kb '(bordersOn France Spain) 'CxUniverse)
           :near-sf    (v/ask? kb '(near Spain France) 'CxUniverse)
           :near-fs    (v/ask? kb '(near France Spain) 'CxUniverse)})
        result (one-outcome-under! "late symmetric mark, then a retraction" ops observe)]
    (testing "and the one outcome is that the retraction reached all of it"
      (is (= {:rows 0 :borders-sf false :borders-fs false :near-sf false :near-fs false}
             result)))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-symmetric-mark-folds-a-pair-two-rules-concluded
  ;; The pair a fold has no bare premise to take: both spellings of one proposition are a
  ;; rule's conclusion, so neither row leaves by having its premise dropped.
  ;; `integrate/fold-supports!` re-hangs the justifications naming the doomed row as their
  ;; consequence onto the survivor, which is what lets the fold run here at all — without
  ;; it the mark arriving first leaves one record and the mark arriving last leaves two,
  ;; each believed, and `(near …)` above the predicate answers the proposition twice.
  ;;
  ;; The two supports are separate rules over separate facts, so the reading also holds
  ;; the belief half: one of them retracted leaves the proposition standing on the other,
  ;; and both retracted take it away.
  (let [ops [[#(v/assert % '(borderClaim Spain France) 'CxUniverse)]
             [#(v/assert % '(treatyClaim France Spain) 'CxUniverse)]
             [#(v/assert % '(symmetric bordersOn) 'CxUniverse)]]
        setup (fn [kb]
                (v/assert-rule kb '[(borderClaim ?x ?y)] '(bordersOn ?x ?y) 'CxUniverse {:direction :forward})
                (v/assert-rule kb '[(treatyClaim ?x ?y)] '(bordersOn ?x ?y) 'CxUniverse {:direction :forward})
                (v/assert kb '(genl bordersOn near) 'CxUniverse))
        rows  (fn [kb] (count (v/sentexes-matching kb '(bordersOn ?x ?y) 'CxUniverse)))
        observe
        (fn [kb]
          {:rows        (rows kb)
           :one-handle? (= (v/handle-of kb '(bordersOn Spain France) 'CxUniverse)
                           (v/handle-of kb '(bordersOn France Spain) 'CxUniverse))
           :near-sf     (v/ask? kb '(near Spain France) 'CxUniverse)
           :near-fs     (v/ask? kb '(near France Spain) 'CxUniverse)
           ;; one support withdrawn: the other still concludes the proposition
           :after-one   (do (v/retract! kb (v/handle-of kb '(borderClaim Spain France)
                                                        'CxUniverse))
                            [(rows kb) (v/ask? kb '(bordersOn Spain France) 'CxUniverse)])
           ;; and with both gone there is nothing left for either spelling to answer
           :after-both  (do (v/retract! kb (v/handle-of kb '(treatyClaim France Spain)
                                                        'CxUniverse))
                            [(rows kb) (v/ask? kb '(bordersOn Spain France) 'CxUniverse)
                             (v/ask? kb '(bordersOn France Spain) 'CxUniverse)])})
        result (one-outcome-under! "late symmetric mark over two rule-concluded spellings"
                                   (cons [setup] ops) observe)]
    (testing "and the one outcome is the mark-first reading"
      (is (= 1 (:rows result)) "one proposition, one record")
      (is (true? (:one-handle? result)))
      (is (every? true? ((juxt :near-sf :near-fs) result))
          "and the predicate above it answers the proposition once, either way round"))
    (testing "belief follows both supports across the fold"
      (is (= [1 true] (:after-one result))
          "one support withdrawn leaves the row standing on the other")
      (is (= [0 false false] (:after-both result))
          "and the second withdrawal takes the whole proposition"))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-computed-context-edge-merges-in-every-ordering
  ;; The calendar case, and the one where the edge nobody asserts is the whole question.
  ;; `contextArgSubrelation` makes January a spec of its year *structurally*, so the
  ;; `genlCx` edge is computed rather than written — and until vaelii#56 the producer
  ;; that computes it ran the exception re-checks and none of the equality reconcilers a
  ;; stated edge runs.  So which of two fillers of one functional slot the KB believed
  ;; came down to whether the year's fact was written before January existed: four
  ;; ingredients, twenty-four orderings, and the ones that mint January last merged
  ;; nothing at all.
  ;;
  ;; The mark lives in the year rather than in CxUniverse because a reified `cx/` context
  ;; is not wired under CxUniverse by anything — the declarations compute its whole ancestor set —
  ;; so a mark left up there is invisible from the calendar and the scenario would be
  ;; asking a different question.  `calendar-op` declares the two reify kinds ahead of
  ;; each op: without them a calendar expression is not a context and the assert is
  ;; refused, which makes them a precondition of the scenario rather than one of its
  ;; arrivals.
  (let [year  '(CxCalFn CxMonad (DatetimeFn "2000"))
        month '(CxCalFn CxMonad (DatetimeFn "2000-01"))
        calendar-op
        (fn [f] (fn [kb]
                  (v/assert kb '(context_denoting_function CxCalFn) 'CxUniverse)
                  (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
                  (f kb)))
        ops [(calendar-op #(v/assert % '(contextArgSubrelation CxCalFn 2 subintervalOf)
                                     'CxUniverse))
             (calendar-op #(v/assert % '(functionalInArg the_best 1) year))
             (calendar-op #(v/assert % '(the_best LaMulanaTwo) year))
             (calendar-op #(v/assert % '(the_best Silksong) month))]
        observe
        (fn [kb]
          {:from-january (sort (map (comp str '?x) (v/ask kb '(the_best ?x) month)))
           :from-year    (sort (map (comp str '?x) (v/ask kb '(the_best ?x) year)))
           :merged?      (boolean (v/same-class? kb 'LaMulanaTwo 'Silksong))})
        result (one-outcome-necessarily! "a computed calendar genlCx edge" ops observe)]
    (testing "and the one outcome is that the computed edge did the merge"
      (is (true? (:merged? result)))
      (is (= ["LaMulanaTwo"] (:from-january result))
          "one filler from below, which is January inheriting the year and merging it")
      (is (= ["LaMulanaTwo"] (:from-year result))
          "and the year, which the merge is not visible from, keeps its own"))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-asymmetric-mark-is-accounted-for-in-every-ordering
  ;; `(asymmetric asBelow)` with both directions of one pair: 6 orderings, and the two
  ;; that put the declaration last are the ones with no entry point left to refuse at — both
  ;; facts are already stored and believed when the mark lands, and the mark reaches back:
  ;; two known-true facts cannot be weighed, so the pair stands in `conflicts`, the answer
  ;; a recover of the same records gives.
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late asymmetric mark" :monotonic
                             ['(asymmetric asBelow) '(asBelow Aa Bb) '(asBelow Bb Aa)]
                             '(asBelow ?x ?y))]
    (testing "the clash is answered exactly once, whichever of the three arrived last"
      (is (= 1 (:accounted invariant))))
    (one-entry-point-each! readings)
    (testing "and the entry point the late mark takes is `conflicts`, with both facts standing"
      (let [late (filterv #(= 2 (count (:believed %))) readings)]
        (is (= 2 (count late)) "two of the six put the mark last")
        (is (every? #(= 1 (:stuck %)) late))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-asymmetric-mark-leaves-the-same-beliefs-in-every-ordering
  ;; The same three sentences at `:default`, where the entry point refuses nothing — an
  ;; `asymmetric` violation refuses only against a known-true converse — so the whole
  ;; believed extent is identical across all 6 and joins the reading, and so is the entry
  ;; point: a represented dilemma, whether a fact or the mark arrived last, since a late
  ;; mark reaches back as a late fact does.
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late asymmetric mark at :default" :default
                             ['(asymmetric asAside) '(asAside Aa Bb) '(asAside Bb Aa)]
                             '(asAside ?x ?y))]
    (testing "both directions stand in every ordering, and the clash is named once"
      (is (= ["(asAside Aa Bb)" "(asAside Bb Aa)"] (:believed invariant)))
      (is (= 1 (:accounted invariant))))
    (is (every? #(= 1 (:weighed %)) readings)
        "every ordering weighs the pair into contradictions")
    (testing "nothing is refused — a default converse is weighed or reported, not turned away"
      (is (every? #(zero? (:refused %)) readings)))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-mark-over-a-transitive-relation-is-accounted-for-in-every-ordering
  ;; The same pair with `(transitive asAbove)` in the scenario: 4 sentences, 24
  ;; orderings, and a second declaration whose own arrival reaches back over the same
  ;; facts.  Transitivity closes the pair into the self-tuples `(asAbove Aa Aa)` and
  ;; `(asAbove Bb Bb)`, which `asymmetric` admits — so the clash under test is still the
  ;; two-way pair, now under a predicate whose extent both marks descend through.
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late mark over a transitive relation" :monotonic
                             ['(transitive asAbove) '(asymmetric asAbove)
                              '(asAbove Aa Bb) '(asAbove Bb Aa)]
                             '(asAbove ?x ?y))]
    (testing "the clash is answered exactly once, whichever of the four arrived last"
      (is (= 1 (:accounted invariant))))
    (one-entry-point-each! readings)
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-anti-transitive-mark-is-accounted-for-in-every-ordering
  ;; The third mark, and the one whose clash is a **triple**: `anti_transitive` convicts
  ;; the two chain steps and the direct step together, so the entry names three halves
  ;; and no two of them are the pair.  4 sentences, 24 orderings.
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late anti_transitive mark" :monotonic
                             ['(anti_transitive parOfx) '(parOfx Aa Bb)
                              '(parOfx Bb Cc) '(parOfx Aa Cc)]
                             '(parOfx ?x ?y))]
    (testing "the chain is answered exactly once, whichever of the four arrived last"
      (is (= 1 (:accounted invariant))))
    (one-entry-point-each! readings)
    (testing "the six orderings that put the mark last leave the chain standing in conflicts"
      (let [late (filterv #(= 3 (count (:believed %))) readings)]
        (is (= 6 (count late)))
        (is (every? #(= 1 (:stuck %)) late))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-functional-mark-is-accounted-for-in-every-ordering
  ;; The second mark, over two fillers no merge can reconcile — `(functional P)` between
  ;; two *symbols* is co-reference and the KB derives an equality from it instead, so a
  ;; clash needs values the partition cannot hold (docs/equality.md).
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late functional mark" :monotonic
                             ['(functional ageOfx) '(ageOfx Aa 3) '(ageOfx Aa 4)]
                             '(ageOfx ?x ?y))]
    (testing "the slot is answered exactly once, whichever of the three arrived last"
      (is (= 1 (:accounted invariant))))
    (one-entry-point-each! readings)
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-mark-answers-the-way-a-late-disjointness-does
  ;; The precedent the choice above is made against, asserted rather than assumed: a late
  ;; `(disjoint A B)` over an already-clashing pair is decided, as a restart decides it.  The
  ;; two must agree entry point for entry point, or the KB is treating "the declaration came last"
  ;; differently according to which declaration it is.
  (let [marked (constraint-outcome! "late asymmetric mark, per entry point" :monotonic
                                    ['(asymmetric asBeside) '(asBeside Aa Bb)
                                     '(asBeside Bb Aa)]
                                    '(asBeside ?x ?y))
        separated (constraint-outcome! "late disjointness, per entry point" :monotonic
                                       ['(disjoint tdogx tcatx) '(tdogx Rexx)
                                        '(tcatx Rexx)]
                                       '(?t Rexx))
        entry-points (fn [{:keys [readings]}]
                       (frequencies (mapv #(-> % (select-keys [:refused :weighed :stuck])
                                               (assoc :reported (count (:reported %))))
                                          readings)))]
    (is (= (:invariant marked) (:invariant separated))
        "one account of the clash, whichever declaration arrived last")
    (is (= (entry-points marked) (entry-points separated))
        "and the same entry points in the same proportions — only the entry kind differs")
    (tu/clear-kb! (tu/test-kb))))

;; ---- retraction and revival ---------------------------------------------

(deftest revival-is-order-independent
  ;; Build the default in either order, defeat it, then retract the defeater. The
  ;; conclusion must come back in both cases — belief is recomputed, not replayed.
  (doseq [build [[#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)
                  #(v/assert % '(bird Sky) 'CxUniverse)]
                 [#(v/assert % '(bird Sky) 'CxUniverse)
                  #(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)]]]
    (let [kb (tu/fresh)]
      (doseq [op build] (op kb))
      (is (seq (v/sentexes-matching kb '(flies Sky) 'CxUniverse)) "the default holds")
      (let [neg (v/assert kb '(not (flies Sky)) 'CxUniverse {:strength :monotonic})]
        (is (empty? (v/sentexes-matching kb '(flies Sky) 'CxUniverse)) "defeated")
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb '(flies Sky) 'CxUniverse)) "revived"))))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-revival-that-owes-a-derivation-is-order-independent
  ;; The revival above only had to *relabel*: the conclusion was still stored, so
  ;; recomputing belief brought it back.  This one owes a **derivation**.  A rule joins
  ;; two facts, one is defeated, and the other arrives while it is OUT — so the join runs
  ;; against a belief-filtered matcher that cannot see the defeated half and no firing is
  ;; ever attempted.  Lifting the defeat then moves a label and leaves nothing behind for
  ;; a blocked set or a refusal record to read, so the conclusion exists only if the
  ;; revived datum went back on the agenda (`vaelii.revived-datum-test`).
  ;;
  ;; `one-outcome-under!` rather than `one-outcome!`, because these ops do not permute
  ;; freely: a lift cannot precede the defeat it lifts, and tying the two together as one
  ;; op would remove the very window this is about — the partner arriving *between* them.
  ;; So the three ordered steps are one chain and the two free ops are chains of one, and
  ;; every interleaving of the three follows.  Twenty orderings, and the ones where the
  ;; partner lands in the middle are the defect.
  (let [assert-a  #(v/assert % '(vpA VOne VTwo) 'CxUniverse)
        defeat-a  #(v/assert % '(not (vpA VOne VTwo)) 'CxUniverse
                             {:strength :monotonic})
        lift-a    #(v/retract! % (v/handle-of % '(not (vpA VOne VTwo)) 'CxUniverse))
        partner   #(v/assert % '(vpB VTwo VThree) 'CxUniverse {:strength :monotonic})
        rule      #(v/assert-rule % '[(vpA ?x ?z) (vpB ?z ?y)] '(vpC ?x ?y) 'CxUniverse
                                  {:direction :forward})
        observe   (fn [kb]
                    {:joined     (boolean (seq (v/sentexes-matching kb '(vpC VOne VThree)
                                                                    'CxUniverse)))
                     :antecedent (boolean (seq (v/sentexes-matching kb '(vpA VOne VTwo)
                                                                    'CxUniverse)))})]
    (is (= {:joined true :antecedent true}
           (one-outcome-under! "a revival that owes a derivation"
                               [[assert-a defeat-a lift-a] [partner] [rule]] observe))
        "a fact that comes back believed must derive what it could not while it was OUT"))
  (tu/clear-kb! (tu/test-kb)))

(deftest an-un-merge-that-owes-a-derivation-is-order-independent
  ;; The same claim as the test above through the **equality** entry point, which reaches it by
  ;; a different route and has to: a merge displaces a spelling with no relabel behind
  ;; it, so the flip is in none of the window sets a revival is read off.  While the
  ;; merge stands the twin joins in the displaced spelling's place, so a partner arriving
  ;; then concludes at the twin — and un-merging sweeps the twin and gives the original
  ;; back, leaving the conclusion to be derived again at the surviving spelling or not at
  ;; all.  Mechanism and the second merge route: `vaelii.revived-datum-test`.
  ;;
  ;; Same shape as its sibling: the ordered steps are one chain, the two free ops are
  ;; chains of one.  The orderings where the partner lands between the merge and the
  ;; un-merge are the defect.
  (let [fact      #(v/assert % '(uqA UDep UZed) 'CxUniverse {:strength :monotonic})
        merge-it  #(v/assert % '(rewriteOf UPref UDep) 'CxUniverse
                             {:strength :monotonic})
        un-merge  #(v/retract! % (v/handle-of % '(rewriteOf UPref UDep) 'CxUniverse))
        partner   #(v/assert % '(uqB UZed UWye) 'CxUniverse {:strength :monotonic})
        rule      #(v/assert-rule % '[(uqA ?x ?z) (uqB ?z ?y)] '(uqC ?x ?y)
                                  'CxUniverse {:direction :forward})
        observe   (fn [kb]
                    {:conclusions (set (map :sentence
                                            (v/sentexes-matching kb '(uqC ?x ?y)
                                                                 'CxUniverse)))
                     :antecedent  (boolean (seq (v/sentexes-matching kb '(uqA UDep UZed)
                                                                     'CxUniverse)))})]
    (is (= {:conclusions #{'(uqC UDep UWye)} :antecedent true}
           (one-outcome-under! "an un-merge that owes a derivation"
                               [[fact merge-it un-merge] [partner] [rule]] observe))
        "a spelling an un-merge gives back must derive what its twin could not"))
  (tu/clear-kb! (tu/test-kb)))

;; ---- two traces, one KB -------------------------------------------------
;;
;; Everything above permutes ONE set of assertions, which can only ask whether the order
;; *within* a trace matters.  A removal makes the stronger question available: two
;; **different** traces that end at the same knowledge must read the same.  That is not a
;; corollary of order independence over adds — the traces are not permutations of each
;; other — and it is the only way to state what a retraction owes, which is to leave
;; nothing of what it took.

(defn- whole-reading
  "**Everything the KB holds**, as content: every stored sentex's sentence and context,
  whether it is believed, and at what class.  Handle-free by construction — a set keyed
  on content, never on the id assertion order hands out — so two KBs reached by
  different routes compare equal exactly when they hold the same knowledge.

  The scenario-specific `observe`s above name the few sentences their scenario is about,
  which is the right instrument when the question is *did this conclusion survive*.  This
  one is for the confluence tests below, where the question is *is anything left over* —
  and a leftover is by definition a sentence the test did not think to name.  Retraction
  sweeps a solely-supported conclusion's record rather than merely relabelling it (the
  claim `tu/assert-neutral!` makes structurally at every teardown), so a sweep that
  stopped short shows up here as an extra member on one side."
  [kb]
  (into #{}
        (map (fn [h]
               (let [sx (v/sentex kb h)]
                 {:sentence (v/sentence-of sx)
                  :context  (:context sx)
                  :believed (v/in? kb h)
                  :class    (v/defeat-class kb h)})))
        (tu/sentex-ids kb)))

(deftest a-fact-given-back-leaves-the-kb-that-never-had-it
  ;; The plainest confluence claim: a KB that learned an extra fact, derived from it and
  ;; gave it back is the KB that never learned it.  Both sides walk every ordering of
  ;; their own trace first, so a difference between them is a difference between the
  ;; traces and not between two arbitrary orders of one.
  (let [rule      #(v/assert-rule % '[(cfA ?x ?z) (cfB ?z ?y)] '(cfC ?x ?y) 'CxUniverse
                                  {:direction :forward})
        lead      #(v/assert % '(cfA CfOne CfTwo) 'CxUniverse)
        keeper    #(v/assert % '(cfB CfTwo CfThree) 'CxUniverse)
        extra     #(v/assert % '(cfB CfTwo CfFour) 'CxUniverse)
        give-back #(v/retract! % (v/handle-of % '(cfB CfTwo CfFour) 'CxUniverse))
        joins     #(set (map :sentence (v/sentexes-matching % '(cfC ?x ?y) 'CxUniverse)))]
    (testing "the extra fact does work while it stands, so the comparison is not vacuous"
      (let [kb (tu/fresh)]
        (doseq [op [rule lead keeper extra]] (op kb))
        (is (= #{'(cfC CfOne CfThree) '(cfC CfOne CfFour)} (joins kb))
            "both partners join the lead")
        (give-back kb)
        (is (= #{'(cfC CfOne CfThree)} (joins kb))
            "and giving one back takes its join and only its join")))
    (is (= (one-outcome! "never larger" [rule lead keeper] whole-reading)
           (one-outcome-under! "larger, then given back"
                               [[rule] [lead] [keeper] [extra give-back]] whole-reading))
        "a KB that learned a fact and gave it back is the KB that never learned it"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-taxonomy-edge-put-back-is-the-edge-that-never-left
  ;; The round trip, over state a retraction has to **rebuild** rather than relabel.  A
  ;; `genl` edge is the sharpest case: it is a cached closure and a reference count, not
  ;; a JTMS label, and `vaelii.taxonomy-teardown-test` exists because nothing in the
  ;; neutral fixture would notice one leaking.  Assert the edge, retract it, assert it
  ;; again — the closure, the membership it fans out to and the rule it lets fire must
  ;; all land where a single assert would have put them, in every interleaving with the
  ;; member and the rule.
  ;;
  ;; Both sides assert at the entry point's own class, because the class is deliberately not
  ;; inherited across a round trip (`a-re-assert-never-downgrades-a-premises-class`) and
  ;; a comparison against a `:monotonic` original would be reading that decision as a bug.
  (let [edge    #(v/assert % '(genl cfdog_t cfmammal_t) 'CxUniverse)
        drop-it #(v/retract! % (v/handle-of % '(genl cfdog_t cfmammal_t) 'CxUniverse))
        member  #(v/assert % '(cfdog_t CfRex) 'CxUniverse)
        rule    #(v/assert % '(implies (cfmammal_t ?x) (cf_breathes ?x)) 'CxUniverse {:direction :forward})
        observe (fn [kb]
                  {:records (whole-reading kb)
                   :genl    (v/genl? kb 'cfdog_t 'cfmammal_t)
                   :specs   (v/specs kb 'cfmammal_t)
                   :types   (set (v/types-of kb 'CfRex))})
        once    (one-outcome! "the edge asserted once" [edge member rule] observe)
        round   (one-outcome-under! "the edge round-tripped"
                                    [[edge drop-it edge] [member] [rule]] observe)]
    (testing "the edge is required, so the comparison is not vacuous"
      (is (true? (:genl once)))
      (is (contains? (:specs once) 'cfdog_t) "the closure fans the subtype in")
      (is (contains? (set (map :sentence (:records once))) '(cf_breathes CfRex))
          "and a rule stated over the supertype reaches the member through it"))
    (is (= once round)
        "an edge retracted and re-asserted leaves what a single assert would have"))
  (tu/clear-kb! (tu/test-kb)))

(deftest two-supports-can-be-withdrawn-in-either-order
  ;; The first scenario here to interleave **two** removals.  Two rules conclude the same
  ;; sentence from two different facts, so the conclusion has two witnesses: withdrawing
  ;; either must leave it standing on the other, and withdrawing both must take it.  The
  ;; sweep is where this goes wrong in both directions — one that collects a closure
  ;; without looking for a surviving witness fails at the first retraction, one that
  ;; leaves a justification behind fails at the second.
  ;;
  ;; 180 orderings rather than the two the withdrawal order alone would give, because the
  ;; retractions are not the only thing moving: a rule arriving after the fact it would
  ;; have fired on has to catch up, and a rule arriving after both retractions has nothing
  ;; to fire on at all.  All of them end in the same place or none of this holds.
  (let [rule-p #(v/assert-rule % '[(cf_p ?x)] '(cf_q ?x) 'CxUniverse {:direction :forward})
        rule-r #(v/assert-rule % '[(cf_r ?x)] '(cf_q ?x) 'CxUniverse {:direction :forward})
        add-p  #(v/assert % '(cf_p CfSubj) 'CxUniverse)
        drop-p #(v/retract! % (v/handle-of % '(cf_p CfSubj) 'CxUniverse))
        add-r  #(v/assert % '(cf_r CfSubj) 'CxUniverse)
        drop-r #(v/retract! % (v/handle-of % '(cf_r CfSubj) 'CxUniverse))
        holds? #(boolean (seq (v/sentexes-matching % '(cf_q CfSubj) 'CxUniverse)))]
    (testing "a withdrawal leaves the conclusion standing on the other witness"
      (doseq [[first-drop second-drop] [[drop-p drop-r] [drop-r drop-p]]]
        (let [kb (tu/fresh)]
          (doseq [op [rule-p rule-r add-p add-r]] (op kb))
          (is (holds? kb) "two witnesses")
          (first-drop kb)
          (is (holds? kb) "one witness left, and one is enough")
          (second-drop kb)
          (is (not (holds? kb)) "and none left is none"))))
    (let [end (one-outcome-under! "both supports withdrawn"
                                  [[add-p drop-p] [add-r drop-r] [rule-p] [rule-r]]
                                  (fn [kb] {:records    (whole-reading kb)
                                            :conclusion (holds? kb)}))]
      (is (false? (:conclusion end))
          "the one outcome is the conclusion gone, not the conclusion kept")
      (is (= 2 (count (:records end)))
          "and what is left is the two rules — no fact, no conclusion, no orphan")))
  (tu/clear-kb! (tu/test-kb)))

;; ---- the taxonomy caches follow suit ------------------------------------

(deftest genl-closure-is-order-independent
  ;; The cached closures are derived state, so they must land in the same place
  ;; whatever order the edges and their defeater arrive in.
  (let [ops [#(v/assert % '(genl sub_t mid_t) 'CxUniverse)
             #(v/assert % '(genl mid_t super_t) 'CxUniverse)
             #(v/assert % '(sub_t Ind1) 'CxUniverse)]
        observe (fn [kb] {:isa (v/isa? kb 'Ind1 'super_t)})]
    (is (= #{{:isa true}} (outcomes (permutations ops) observe))
        "transitive membership does not depend on which edge was asserted first"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-firing-that-subsumes-is-order-independent
  ;; The closure landing in the same place is not enough: matching fans an antecedent
  ;; over its spec closure, so a `genl` edge changes which antecedents the *stored*
  ;; facts satisfy.  The arriving datum is the edge, and firing the rules keyed on
  ;; `genl` is not the same thing as re-firing the rules the edge just connected — so
  ;; without `special/subsumption-seeds` these four sentences derive `(breathes Muffet)`
  ;; in the orders that put the edge before the fact and nothing in the others.
  ;;
  ;; The rule is stated over `thing`, the top of a two-edge closure `dog_t ⊑ animal_t ⊑
  ;; thing`, so `one-outcome-necessarily!` holds both edges to account: Muffet reaches the
  ;; antecedent only down the whole spec fan, and dropping either edge leaves the fact
  ;; short of `thing` and the conclusion undrawn.  A rule stated over `animal_t` instead
  ;; would reach Muffet through the single `dog_t ⊑ animal_t` edge and leave
  ;; `animal_t ⊑ thing` moving no field of the reading — an edge the scenario names and
  ;; does not test.
  (let [ops [#(v/assert % '(genl animal_t thing) 'CxUniverse)
             #(v/assert % '(genl dog_t animal_t) 'CxUniverse)
             #(v/assert % '(implies (thing ?x) (breathes ?x)) 'CxUniverse {:direction :forward})
             #(v/assert % '(dog_t Muffet) 'CxUniverse)]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(breathes Muffet) 'CxUniverse)))})]
    (is (= {:derived true} (one-outcome-necessarily! "subsumption firing" ops observe))
        "and the one outcome is the conclusion, not the silence"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-firing-that-sees-across-a-context-edge-is-order-independent
  ;; The same claim for the other closure, and the same gap.  Matching fans an
  ;; antecedent up the *visibility* ancestor set, so a `genlCx` edge changes which facts a
  ;; stored rule can see — and the arriving datum is again the edge, so firing the rules
  ;; keyed on `genlCx` is not the same thing as re-joining the rules the edge just
  ;; gave a wider view.  Without `special/visibility-seeds` these three sentences derive
  ;; `(v_seen_p VA)` only when the edge arrives before the rule or the fact, and nothing
  ;; when it arrives after both.  The rule sees the fact through the one
  ;; `(genlCx CxVLow CxVMid)` edge, so `one-outcome-necessarily!` holds the edge to
  ;; account: dropping it leaves the rule blind and the conclusion undrawn.
  (let [ops [#(v/assert % '(genlCx CxVLow CxVMid) 'CxUniverse)
             #(v/assert % '(v_fact_p VA) 'CxVMid)
             #(v/assert % '(implies (v_fact_p ?x) (v_seen_p ?x)) 'CxVLow {:direction :forward})]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(v_seen_p VA) 'CxVLow)))})]
    (is (= {:derived true} (one-outcome-necessarily! "visibility firing" ops observe))
        "a rule fires off what its context can see, whenever it was told it could"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-subsumed-firing-across-a-context-edge-is-order-independent
  ;; The two closures at once, which is the shape neither seeding covers on its own.
  ;; `special/visibility-seeds` enumerates from `:rule-antecedents`, so a rule taking
  ;; `(vs_dog_t ?x)` sends it to the facts filed under `vs_dog_t` — and the fact that
  ;; answers that antecedent is filed under `vs_terrier_t`, matchable only down the
  ;; `genl` spec fan (`roster-antecedent-functors` is what walks it).  Four sentences: the
  ;; `(genlCx CxSLow CxSMid)` edge arriving last has to re-join the rule over a fact one
  ;; type below the antecedent it names.  Every one of the four is necessary — the edge for
  ;; visibility, the `genl` edge for the spec fan, the fact, and the rule — so this runs
  ;; under `one-outcome-necessarily!`.
  (let [ops [#(v/assert % '(genlCx CxSLow CxSMid) 'CxUniverse)
             #(v/assert % '(genl vs_terrier_t vs_dog_t) 'CxSMid {:strength :monotonic})
             #(v/assert % '(vs_terrier_t SRex) 'CxSMid {:strength :monotonic})
             #(v/assert % '(implies (vs_dog_t ?x) (vs_seen_p ?x)) 'CxSLow {:direction :forward})]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(vs_seen_p SRex) 'CxSLow)))})]
    (is (= {:derived true} (one-outcome-necessarily! "subsumed visibility firing" ops observe ordering-sample))
        "a rule fires off a subtype of what its antecedent names, in any arrival order"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-negated-antecedent-firing-across-a-context-edge-is-order-independent
  ;; The negated-antecedent twin of the visibility case, and the same gap on the other
  ;; branch: `special/visibility-seeds` looked a negated antecedent's roster key
  ;; `[:not v_neg_p]` up in the functor-root index, which nothing is written under, so a
  ;; genlCx edge arriving after the negative fact never re-joined the rule.  These three
  ;; sentences must derive `(v_neg_seen_p VA)` in every arrival order, not only the ones
  ;; that put the edge before the rule and the fact.  The rule reaches the negative fact
  ;; through the one `(genlCx CxVNLow CxVNMid)` edge, so the edge is necessary and this
  ;; runs under `one-outcome-necessarily!`.
  (let [ops [#(v/assert % '(genlCx CxVNLow CxVNMid) 'CxUniverse)
             #(v/assert % '(not (v_neg_p VA)) 'CxVNMid {:strength :monotonic})
             #(v/assert % '(implies (not (v_neg_p ?x)) (v_neg_seen_p ?x)) 'CxVNLow {:direction :forward})]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(v_neg_seen_p VA) 'CxVNLow)))})]
    (is (= {:derived true} (one-outcome-necessarily! "negated visibility firing" ops observe))
        "a rule with a negated antecedent fires off what its context can see, in any order"))
  (tu/clear-kb! (tu/test-kb)))

(defn- a-late-edge-withdraws-what-the-blocker-blocks!
  "Walk every ordering of `rule` (stated in the unwired context `k`), `(le_p LeA)` in `k`
  and `(le_q LeA)` in CxUniverse, first without and then with `(genlCx k CxUniverse)`.
  Without the edge `k` cannot see the blocker, so `(le_r LeA)` is derived; with it the
  blocker is visible and the conclusion is withdrawn, whichever of the four arrived last.

  Two `one-outcome!` walks, not `one-outcome-necessarily!`: the rule and the `le_p` fact
  are redundant for the withheld conclusion — dropping either keeps it absent — so the
  edge-free walk is what shows both do work, as the `naf-over-a-merged-term` test above
  records for the same shape."
  [label rule k]
  (let [base    [#(v/assert % rule k {:direction :forward})
                 #(v/assert % '(le_p LeA) k)
                 #(v/assert % '(le_q LeA) 'CxUniverse)]
        edge    #(v/assert % (list 'genlCx k 'CxUniverse) 'CxUniverse)
        observe (fn [kb]
                  (let [h (v/handle-of kb '(le_r LeA) k)]
                    {:derived (boolean (and h (v/in? kb h)))}))]
    (is (= {:derived true} (one-outcome! (str label ", no edge") base observe))
        "the blocker is invisible from the unwired context, so the rule fires")
    (is (= {:derived false} (one-outcome! label (conj base edge) observe))
        "the edge makes the blocker visible, so the conclusion is withdrawn in every order"))
  (tu/clear-kb! (tu/test-kb)))

(deftest an-unknown-antecedent-reads-a-blocker-a-late-context-edge-reveals
  ;; A context with no `genlCx` edge sees nothing of CxUniverse, so an `(unknown S)`
  ;; antecedent there holds over an `S` stored in CxUniverse.  Wiring the context under
  ;; CxUniverse afterwards makes `S` visible, and the firing the edge-free state licensed
  ;; has to be swept, exactly as when the edge arrived first.
  (a-late-edge-withdraws-what-the-blocker-blocks!
   "unknown under a late edge"
   '(set/forwardRule (implies (and (le_p ?x) (unknown (le_q ?x))) (le_r ?x)))
   'CxLateNafK))

(deftest an-exception-reads-a-blocker-a-late-context-edge-reveals
  ;; The `exceptWhen` spelling of the same claim: the exception query is asked from the
  ;; rule's context, so the edge that widens that context's ancestor set decides it.
  (a-late-edge-withdraws-what-the-blocker-blocks!
   "exceptWhen under a late edge"
   '(exceptWhen (le_q ?x) (set/forwardRule (implies (le_p ?x) (le_r ?x))))
   'CxLateExcK))

(deftest a-rule-above-fires-on-the-facts-of-a-context-newly-wired-under-it
  ;; the other direction of the same edge, and the one that survives a fix taking only
  ;; the first: a rule stated *above* applies in every context that sees it, so wiring a
  ;; new context under it hands the rule that context's own facts and places
  ;; the conclusion there.  Seeding is by fact, so it has to reach both the fact-above case
  ;; the sibling above covers and this rule-above case.  Three sentences: the rule in
  ;; `CxXMid` reaches `CxXLow`'s fact through the one `(genlCx CxXLow CxXMid)` edge, so the
  ;; edge is necessary and this runs under `one-outcome-necessarily!`.
  (let [ops [#(v/assert % '(genlCx CxXLow CxXMid) 'CxUniverse)
             #(v/assert % '(x_fact_p XB) 'CxXLow)
             #(v/assert % '(implies (x_fact_p ?x) (x_seen_p ?x)) 'CxXMid {:direction :forward})]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(x_seen_p XB) 'CxXLow)))})]
    (is (= {:derived true} (one-outcome-necessarily! "inherited-rule firing" ops observe))
        "a rule above is inherited into a context wired under it, whenever that happened"))
  (tu/clear-kb! (tu/test-kb)))

;; ---- a context edge widens what a merge reaches -------------------------

(defn- merged-spelling-observe
  "The reading a merge-across-a-context-edge scenario is judged by: the sentences the
  KB actually answers with on `pred`, both spellings asked at the backward entry point, and
  the partition itself.

  All three are needed and none of them alone is.  A sentex whose spelling a merge
  retired stays *believed* — supersession subtracts reported belief, not the label — so
  a belief reading alone calls two orderings equal while one of them answers no query at
  all.  The partition is read beside them because it is the half that cannot vary here:
  it agrees in every ordering, so a disagreement in the other two names **migration**
  rather than the closure."
  [pred old new ctx]
  (fn [kb]
    {:answered (set (map :sentence (v/sentexes-matching kb (list pred '?x) ctx)))
     :asked    [(v/ask? kb (list pred old) ctx) (v/ask? kb (list pred new) ctx)]
     :equiv    (v/equiv-class kb old ctx)}))

(deftest a-merge-above-a-context-edge-restates-the-facts-it-newly-reaches
  ;; An equality applies where it is **visible**, so which sentexes it restates is as
  ;; much a question about the genlCx ancestor set as about the closure — and the arriving datum
  ;; is again the edge.  `(equals MTom MThomas)` in `CxMUp` cannot displace
  ;; `(m_fact_p MTom)` in `CxMLow` until `(genlCx CxMLow CxMUp)` says `CxMLow` can see it —
  ;; so without `special/migrate-under-context-edge` the two orderings that wire the
  ;; contexts last keep the spelling `CxMLow` stored the fact in, while every read from
  ;; `CxMLow` asks after the representative: believed, and answering no query under
  ;; either name.  The supersession reconcile cannot cover it, since an entry there is
  ;; only ever dropped or restated and this one was never written.
  (let [ops [#(v/assert % '(genlCx CxMLow CxMUp) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(equals MTom MThomas) 'CxMUp {:strength :monotonic})
             #(v/assert % '(m_fact_p MTom) 'CxMLow {:strength :monotonic})]]
    (is (= {:answered '#{(m_fact_p MThomas)} :asked [true true] :equiv '#{MTom MThomas}}
           (one-outcome-necessarily! "a merge above a context edge" ops
                                     (merged-spelling-observe 'm_fact_p 'MTom 'MThomas 'CxMLow)))
        "the reader that newly sees the merge reads the fact under the name it elected"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-merge-below-a-context-edge-restates-the-facts-it-newly-sees
  ;; The other direction of the same edge, and the one a fix taking only the first
  ;; leaves broken: the merge sits in `CxNLow` and the fact above it in `CxNUp`, so what
  ;; the edge newly hands the reader is the *fact* rather than the merge.  `CxNUp` has
  ;; been told nothing and keeps its own spelling; `CxNLow` elects the representative and
  ;; owes a restatement of its own.
  (let [ops [#(v/assert % '(genlCx CxNLow CxNUp) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(equals NTom NThomas) 'CxNLow {:strength :monotonic})
             #(v/assert % '(n_fact_p NTom) 'CxNUp {:strength :monotonic})]
        observe (fn [kb]
                  (assoc ((merged-spelling-observe 'n_fact_p 'NTom 'NThomas 'CxNLow) kb)
                         :above (set (map :sentence
                                          (v/sentexes-matching kb '(n_fact_p ?x) 'CxNUp)))))]
    (is (= {:answered '#{(n_fact_p NThomas)} :asked [true true] :equiv '#{NTom NThomas}
            :above '#{(n_fact_p NTom)}}
           (one-outcome-necessarily! "a merge below a context edge" ops observe))
        "the reader below restates the fact for itself and leaves the original where it lives"))
  (tu/clear-kb! (tu/test-kb)))

;; ---- a context edge widens what a mark derives, not only what it restates -
;;
;; The two tests above cover an `equals` that is already stored becoming newly visible.
;; These cover the sharper gap `special/equate-under-context-edge` closes: no `equals`
;; exists anywhere until the widened ancestor set makes two `functional` (or `anti_symmetric`)
;; fillers jointly visible for the first time — the mark, the two fillers and the
;; `genlCx` edge are the fourth arrival order of one merge, matching the three
;; `derive-functional-equalities` / `equate-existing` / `equate-under-edge` already own.
;;
;; **Not a free permutation of all four**, and that is a finding rather than a
;; simplification.  `one-outcome!` over the full 24 orderings reds on exactly the six
;; where the *filler in the wider context* (`CxFuUp`) is asserted dead last, after the
;; mark, the other filler and the edge are all already in place — every one of those six
;; fails identically on unmodified `main`, so it is a pre-existing gap in the plain
;; **fact-arrives** trigger (`core.clj`'s `derive-functional-equalities` call scopes the
;; clash search to the arriving fact's *own* context, never to a reader below it that
;; already sees that context through a standing `genlCx` edge), not something this arm
;; introduces or is positioned to fix — its own trigger is the edge, and in all six the
;; edge is not what arrived last.  Scoping to the literal shape issue #43 asks for —
;; the edge arriving last, with the mark and both fillers free among themselves before
;; it — is exactly the six orderings that are unaffected by that other gap, and every one
;; of them is green.  Filed as a follow-up rather than fixed here: closing it changes the
;; cost of every ordinary assert under a marked predicate, not only the `genlCx` path
;; this issue is about, and deserves its own review.
(defn- one-outcome-edge-last!
  "`one-outcome!`'s reading, restricted to the orderings that put `edge-op` **last**
  after every permutation of `free-ops` — the shape `one-outcome!` cannot express, since
  its chains interleave freely rather than pinning one op to the tail of every walk.
  Built from the namespace's own `permutations` and `outcome-census` rather than a new
  helper of its own, since one caller does not earn a third combinator beside
  `one-outcome!` / `one-outcome-under!`."
  [label free-ops edge-op observe]
  (let [trials (mapv #(conj (vec %) edge-op) (permutations free-ops))
        census (outcome-census trials observe)]
    (is (= 1 (count census))
        (str label ": " (count census) " distinct outcomes across " (count trials)
             " orderings with the edge last —" (census-report census)))
    (key (first (sort-by (comp :at val) census)))))

(deftest a-functional-mark-derives-when-a-context-edge-arrives-last
  (let [mark    #(v/assert % '(functional fuP) 'CxFuUp)
        fact-up #(v/assert % '(fuP FuTom FuV1) 'CxFuUp)
        fact-lo #(v/assert % '(fuP FuTom FuV2) 'CxFuLow)
        edge    #(v/assert % '(genlCx CxFuLow CxFuUp) 'CxUniverse {:strength :monotonic})
        observe (fn [kb]
                  {:merged (boolean (v/same-class? kb 'FuV1 'FuV2 'CxFuLow))
                   :equals (some? (v/handle-of kb '(equals FuV1 FuV2) 'CxFuLow))})]
    (is (= {:merged true :equals true}
           (one-outcome-edge-last! "functional mark, context edge arriving last"
                                   [mark fact-up fact-lo] edge observe))
        "whichever order the mark and the two fillers arrived in, the reader below
         derives the equality once the edge that joins it to both lands — matching what
         `equate-existing` and `equate-under-edge` already guarantee for their own
         arrival orders"))
  (tu/clear-kb! (tu/test-kb)))

(deftest an-antisymmetric-mark-derives-when-a-context-edge-arrives-last
  ;; The antisymmetric twin, over a converse pair instead of two fillers of one argument
  ;; — `relation_properties_test/an-antisymmetric-converse-derives-an-equality` is the
  ;; same clash in one context; this is that clash split across the widened ancestor set.  Same
  ;; scoping as the functional test above and for the identical reason: the converse in
  ;; the wider context (`CxAuUp`) arriving dead last hits the same pre-existing
  ;; fact-arrival gap, unrelated to this arm's own trigger.
  (let [mark     #(v/assert % '(anti_symmetric auP) 'CxAuUp)
        conv-up  #(v/assert % '(auP AuAlice AuBob) 'CxAuUp)
        conv-low #(v/assert % '(auP AuBob AuAlice) 'CxAuLow)
        edge     #(v/assert % '(genlCx CxAuLow CxAuUp) 'CxUniverse {:strength :monotonic})
        observe  (fn [kb]
                   {:merged (boolean (v/same-class? kb 'AuAlice 'AuBob 'CxAuLow))
                    :equals (some? (v/handle-of kb '(equals AuAlice AuBob) 'CxAuLow))})]
    (is (= {:merged true :equals true}
           (one-outcome-edge-last! "antisymmetric mark, context edge arriving last"
                                   [mark conv-up conv-low] edge observe))
        "the converse forces the merge from the reader below once the edge that joins it
         to both lands, however the mark and the two directions arrived"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-functional-mark-merges-across-a-context-edge-regardless-of-unrelated-kb-noise
  ;; b3bfb23b (#43 follow-up): `special/equate-under-context-edge`'s candidate walk
  ;; once read every stored fact under *any* functional/functionalInArg-marked
  ;; predicate anywhere in the KB, capped only by `*exposure-instance-budget*` with no
  ;; relationship to the arriving edge's own contexts.  Past a KB-wide size threshold
  ;; that made the cut depend on handle-assignment order: the same three facts and two
  ;; edges, asserted in a different order, merged in one ordering and not another --
  ;; an outright order-independence violation, not only a completeness gap.  The fix
  ;; (`context-edge-reader-ancestors`) scopes the walk to what the edge itself connects, so
  ;; an unrelated marked predicate's own noise -- however much of it, and whichever
  ;; side of the merge's own ops it lands on -- must never change whether this merge
  ;; completes.  The budget is bound well below the noise's size so an unscoped walk
  ;; would have spent it entirely on the noise before ever reaching this scenario's own
  ;; three facts.
  (let [mark    #(v/assert % '(functional nzP) 'CxNzUp)
        fact-up #(v/assert % '(nzP NzTom NzV1) 'CxNzUp)
        fact-lo #(v/assert % '(nzP NzTom NzV2) 'CxNzLow)
        edge    #(v/assert % '(genlCx CxNzLow CxNzUp) 'CxUniverse {:strength :monotonic})
        noise   #(do (v/assert % '(functional nzNoiseP) 'CxNzNoise)
                     (dotimes [i 12]
                       (v/assert % (list 'nzNoiseP (tu/tmp-ind (str "NzSubj" i)) i)
                                 'CxNzNoise)))
        observe (fn [kb]
                  {:merged (boolean (v/same-class? kb 'NzV1 'NzV2 'CxNzLow))
                   :equals (some? (v/handle-of kb '(equals NzV1 NzV2) 'CxNzLow))})]
    (binding [tax/*exposure-instance-budget* 4]
      (is (= {:merged true :equals true}
             (one-outcome-edge-last! "functional mark, context edge last, KB-wide noise"
                                     [mark fact-up fact-lo noise] edge observe))
          "an unrelated marked predicate's own noise must not change whether -- or in
           which orderings -- the edge-triggered merge completes")))
  (tu/clear-kb! (tu/test-kb)))

;; ---- a rule reaching a merged term concludes once -----------------------

(deftest a-rule-over-a-merged-term-concludes-at-the-elected-spelling-in-every-order
  ;; A merge retires a spelling without moving a label — supersession is deliberately
  ;; not a forced OUT inside the fixpoint, since the twin is justified by the spelling it
  ;; displaced (docs/equality.md).  So without the gate in `chain/process-datum` a retired
  ;; spelling reaching the chaining agenda draws a conclusion that stays *believed* under
  ;; a name no read asks after, where the same three sentences in any other order
  ;; conclude once.  The two orderings with both the merge and the rule ahead of the fact
  ;; are the ones that put the fact on the agenda already displaced.
  ;;
  ;; The believed set is read as well as the answer set, and that is the point: what
  ;; splits here is a sentence the KB believes and retrieval never returns, which an
  ;; answer-set reading alone calls agreement.
  (let [ops [#(v/assert % '(equals RTom RThomas) 'CxROne {:strength :monotonic})
             #(v/assert % (default-rule '[(r_mammal_p ?x)] '(r_fur_p ?x)) 'CxROne)
             #(v/assert % '(r_mammal_p RTom) 'CxROne {:strength :monotonic})]
        observe (fn [kb]
                  {:answered (set (map :sentence (v/sentexes-matching kb '(r_fur_p ?x) 'CxROne)))
                   :asked    [(v/ask? kb '(r_fur_p RTom) 'CxROne)
                              (v/ask? kb '(r_fur_p RThomas) 'CxROne)]
                   :believed (into #{}
                                   (comp (filter #(v/in? kb %))
                                         (keep #(some-> (v/sentex kb %) :sentence))
                                         (filter #(contains? '#{r_mammal_p r_fur_p} (first %))))
                                   (tu/sentex-ids kb))})]
    (is (= {:answered '#{(r_fur_p RThomas)}
            :asked    [true true]
            :believed '#{(r_mammal_p RThomas) (r_fur_p RThomas)}}
           (one-outcome-necessarily! "a rule over a merged term" ops observe))
        "the rule fires at the elected spelling only, whenever the merge arrived"))
  (tu/clear-kb! (tu/test-kb)))

;; The ops are shared by the sampled test and the exhaustive one, so the two cannot
;; drift into checking different things — the only difference between them is how many
;; of the 24 orderings they walk.  No op places CxWMid under CxUniverse.  The edge rule
;; and the `wWireP` fact both sit in CxUniverse and fire there, and a `genlCx` edge is
;; read globally (`taxonomy/relation-scope`), so neither CxWMid nor CxWLow reads anything
;; out of CxUniverse.  That edge therefore moves no reading, and the necessity check in
;; `one-outcome-necessarily!` refuses it.
(def ^:private derived-edge-ops
  [#(v/assert % '(w_fact_p WA) 'CxWMid)
   #(v/assert % '(implies (w_fact_p ?x) (w_seen_p ?x)) 'CxWLow {:direction :forward})
   #(v/assert % '(wWireP CxWLow CxWMid) 'CxUniverse)
   #(v/assert % '(implies (wWireP ?a ?b) (genlCx ?a ?b)) 'CxUniverse {:direction :forward})])

(defn- derived-edge-observe [kb]
  {:derived (boolean (seq (v/sentexes-matching kb '(w_seen_p WA) 'CxWLow)))})

(deftest a-derived-context-edge-seeds-like-an-asserted-one
  ;; and a rule concluding the edge reaches the same belief an assert does, or the
  ;; fixpoint would depend on whether the spindle was written or inferred.
  ;;
  ;; Four orderings, chosen for the positions that matter: the edge rule first and last,
  ;; and the fact arriving before and after the wiring that has to reach it.  The test
  ;; below walks a broader deterministic sample.
  (doseq [order [[0 1 2 3] [3 2 1 0] [1 3 2 0] [0 2 3 1]]]
    (let [ops (mapv derived-edge-ops order)
          kb  (tu/fresh)]
      (doseq [op ops] (op kb))
      (is (= {:derived true} (derived-edge-observe kb))
          (str order ": a derived edge has to seed what an asserted one seeds"))))
  (tu/clear-kb! (tu/test-kb)))

(deftest orderings-of-a-derived-context-edge-agree
  ;; The broad form of the 4-ordering test above: a deterministic sample of 16 of the 24
  ;; orderings (`ordering-sample`).  The sample walks the identity, the reverse and a
  ;; fixed-seed spread between them; raise `ordering-sample` or drop the cap for an
  ;; exhaustive audit.
  (is (= {:derived true}
         (one-outcome-necessarily! "derived visibility firing" derived-edge-ops derived-edge-observe
                                   ordering-sample))
      "a derived edge has to seed what an asserted one seeds, over a sample of orderings")
  (tu/clear-kb! (tu/test-kb)))

;; ---- belief projection reads its answer from current state, in any order ----

(deftest belief-projection-is-order-independent
  ;; The modal projector answers `(believes Agent P)` by running `P` through the whole
  ;; registry in the agent's own context, so its answers must not depend on the order the
  ;; grant, the belief facts, and a genl edge a belief rests on arrived — nor on the order
  ;; two agents' contradictory beliefs landed: the two share no context, so the pair must
  ;; never surface as a contradiction under any ordering.  5 assertions, 120 orderings.
  (let [alice (v/context-of-agent 'Alice)
        bob   (v/context-of-agent 'Bob)
        ops [#(v/assert % '(modal_predicate believes) 'CxUniverse)  ; the grant
             #(v/assert % '(flies Tweety) alice)                   ; Alice believes it
             #(v/assert % '(not (flies Tweety)) bob)               ; Bob believes the opposite
             #(v/assert % '(genl finch7 bird7) alice)              ; a taxonomy edge in Alice's ctx
             #(v/assert % '(finch7 Jack) alice)]                   ; so Alice believes (bird7 Jack)
        observe (fn [kb]
                  {:alice-flies    (v/ask? kb '(believes Alice (flies Tweety)) 'CxUniverse)
                   :bob-notflies   (v/ask? kb '(believes Bob (not (flies Tweety))) 'CxUniverse)
                   :alice-notflies (v/ask? kb '(believes Alice (not (flies Tweety))) 'CxUniverse)
                   :alice-bird     (v/ask? kb '(believes Alice (bird7 Jack)) 'CxUniverse)
                   :contradictions (count (v/contradictions kb))})
        result (one-outcome-necessarily! "belief projection" ops observe)]
    (testing "and the one outcome is the intended reading"
      (is (true? (:alice-flies result)))
      (is (true? (:bob-notflies result)))
      (is (false? (:alice-notflies result)) "no cross-agent leakage, in any order")
      (is (true? (:alice-bird result)) "the projection reaches the genl closure")
      (is (zero? (:contradictions result)) "isolated agents raise no contradiction")))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-symmetric-antecedent-is-order-independent-at-either-position
  ;; A symmetric fact is stored in one orientation and *means* both, and the two ways a
  ;; rule reaches it disagreed about that: the join probes both argument orders, while
  ;; the trigger unified the arriving fact as written.  So the combination that needed
  ;; the mirror was enumerated by nobody when the symmetric fact arrived **second**, and
  ;; the same three sentences derived the conclusion or not depending on which was last.
  ;; 6 orderings, and the fourth reading below is the full join, which was always right.
  (let [ops     [#(v/assert % '(symmetric sibOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(implies (and (ownsPet ?o ?a) (sibOf ?a ?b)) (alsoOwns ?o ?b))
                            'CxUniverse {:direction :forward})
                 #(v/assert % '(ownsPet Bob Tib) 'CxUniverse)
                 #(v/assert % '(sibOf Rex Tib) 'CxUniverse)]
        observe (fn [kb]
                  {:mirrored (boolean (seq (v/sentexes-matching kb '(alsoOwns Bob Rex) 'CxUniverse)))
                   ;; `mapv`: the extent readers are lazy over live state, and this map
                   ;; outlives the KB the ordering walk built it from
                   :supports (mapv #(count (:support (v/why kb (:id %))))
                                   (v/sentexes-matching kb '(alsoOwns ?o ?b) 'CxUniverse))
                   :conflicts (count (v/conflicts kb))})
        result  (one-outcome-necessarily! "symmetric antecedent" ops observe)]
    (testing "and the one outcome is the join's reading"
      (is (true? (:mirrored result))
          "the pair the mirror makes is derived whichever fact arrived second")
      (is (= [1] (:supports result))
          "one conclusion, justified once — the mirror of a fact is not a second premise")
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-symmetric-fact-reaches-a-rule-stated-over-its-super-predicate
  ;; The mirror is the *fact's* own declaration, and the antecedent that has to see it
  ;; need not be written at the fact's own predicate: `(genl gsibOf gkinOf)` puts a
  ;; `gkinOf` antecedent above a `gsibOf` fact, so the pairs that antecedent reaches
  ;; move when `gsibOf` is declared symmetric.  Both halves of the reach have to fan the
  ;; sub-predicates — the trigger's mirror, and the re-join a late declaration owes — and
  ;; either one reading only the antecedent's own functor loses the conclusion in the
  ;; orderings that put the fact or the declaration last.  5 assertions, 120 orderings.
  ;;
  ;; The super-predicate carries facts of its own beside the sub's, which is the
  ;; arrangement a real hierarchy is in and the one that makes the conclusion **set** the
  ;; claim rather than its count: a mirror taken where the pair does not call for one, or
  ;; a super-predicate fact give the impression that it were symmetric, both read as an extra
  ;; conclusion rather than as nothing at all.  They arrive with the sub's fact as one op
  ;; — what the orderings are about is where the *declaration*, the edge and the rule fall
  ;; against the facts, not how the facts fall against each other.
  (let [ops     [#(v/assert % '(symmetric gsibOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(genl gsibOf gkinOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(implies (and (gownsPet ?o ?a) (gkinOf ?a ?b)) (gAlsoOwns ?o ?b))
                            'CxUniverse {:direction :forward})
                 #(v/assert % '(gownsPet Bob Tib) 'CxUniverse)
                 #(do (v/assert % '(gsibOf Rex Tib) 'CxUniverse)
                      (doseq [[a b] '[[Ann Bea] [Cal Dee] [Eve Fay] [Gil Hal] [Ida Jem]]]
                        (v/assert % (list 'gkinOf a b) 'CxUniverse)))]
        observe (fn [kb]
                  (let [cs (v/sentexes-matching kb '(gAlsoOwns ?o ?b) 'CxUniverse)]
                    {:conclusions (set (map :sentence cs))
                     ;; sorted: the extent readers promise the set, not the order
                     :supports    (vec (sort (map #(count (:support (v/why kb (:id %)))) cs)))
                     :conflicts   (count (v/conflicts kb))}))
        result  (one-outcome-necessarily! "symmetric under a super-predicate" ops observe)]
    (testing "and the one outcome is the mirrored pair, derived once"
      (is (= '#{(gAlsoOwns Bob Rex)} (:conclusions result))
          "the sub-predicate's mirror reaches an antecedent stated above it")
      (is (= [1] (:supports result))
          "one conclusion, justified once — the mirror of a fact is not a second premise")
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-symmetric-antecedent-mid-chain-is-order-independent
  ;; The 4-op case above the previous two has the symmetric literal at the rule's last
  ;; antecedent, where the trigger and the join are the only two readers.  Here it sits
  ;; **between** two others, so the mirror has to hold whichever way the completion runs:
  ;; the symmetric fact arriving last triggers at the middle position and both neighbours
  ;; are joined outward from the mirrored binding, while either neighbour arriving last
  ;; reaches the middle by a join from one side and the far one by a join from the other.
  ;; 5 assertions, 120 orderings, and only `(mSpans Bo Zed)` is entailed — a mirror
  ;; applied where the chain does not need one would show up as a second conclusion.
  (let [ops     [#(v/assert % '(symmetric mlinkOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(implies (and (mheadOf ?o ?a) (mlinkOf ?a ?b) (mtailOf ?b ?c))
                                        (mSpans ?o ?c))
                            'CxUniverse {:direction :forward})
                 #(v/assert % '(mheadOf Bo Tib) 'CxUniverse)
                 #(v/assert % '(mlinkOf Rex Tib) 'CxUniverse)
                 #(v/assert % '(mtailOf Rex Zed) 'CxUniverse)]
        observe (fn [kb]
                  (let [cs (v/sentexes-matching kb '(mSpans ?o ?c) 'CxUniverse)]
                    {:conclusions (set (map :sentence cs))
                     :supports    (vec (sort (map #(count (:support (v/why kb (:id %)))) cs)))
                     :conflicts   (count (v/conflicts kb))}))
        result  (one-outcome-necessarily! "symmetric mid-chain" ops observe)]
    (testing "and the one outcome is the chain the mirror closes, derived once"
      (is (= '#{(mSpans Bo Zed)} (:conclusions result)))
      (is (= [1] (:supports result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-symmetric-fact-does-not-mirror-what-was-not-declared-symmetric
  ;; The mirror is the *fact's* own declaration, not its supertype's: `sibOf` being
  ;; symmetric says nothing about a `knowsOf` fact, and a rule over one must not read a
  ;; pair the KB never stated.
  (let [kb (tu/test-kb)]
    (tu/clear-kb! kb)
    (v/assert kb '(implies (likesOf ?a ?b) (fanOf ?a ?b)) 'CxUniverse {:direction :forward})
    (v/assert kb '(likesOf Ann Bea) 'CxUniverse)
    (is (= '[(fanOf Ann Bea)]
           (mapv :sentence (v/sentexes-matching kb '(fanOf ?a ?b) 'CxUniverse)))
        "no mirrored conclusion off an undeclared predicate")
    (tu/clear-kb! kb)))

(deftest a-symmetric-fact-mirrors-from-the-lead-position-too
  ;; The sibling of the test above, with the arrangement that hides the defect removed.
  ;; There, the super-predicate carries five facts of its own, which is enough to move the
  ;; planner off leading the join with the symmetric literal.  Here it carries none, so
  ;; `(gkinOf ?a ?b)` is the cheapest literal and leads — and a lead-position match is the
  ;; one place a symmetric fact's mirror was dropped, because both retrieval paths deduped
  ;; the mirror probe by **handle**: an all-variable pattern binds one stored fact twice
  ;; and differently, and the second binding was read as a repeat of the first.
  ;;
  ;; It failed forward *and* backward, which is what says the defect was in the matcher
  ;; rather than in chaining: 48 of these 120 orderings derived nothing, and `prove` of
  ;; the mirrored pair failed in exactly those.  Both readings are here for that reason.
  (let [ops     [#(v/assert % '(symmetric lsibOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(genl lsibOf lkinOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(implies (and (lownsPet ?o ?a) (lkinOf ?a ?b)) (lAlsoOwns ?o ?b))
                            'CxUniverse {:direction :forward})
                 #(v/assert % '(lownsPet Bob Tib) 'CxUniverse)
                 #(v/assert % '(lsibOf Rex Tib) 'CxUniverse)]
        observe (fn [kb]
                  {:conclusions (set (map :sentence (v/sentexes-matching
                                                     kb '(lAlsoOwns ?o ?b) 'CxUniverse)))
                   ;; the backward half of the same question, asked of the mirror
                   :proved      (boolean (seq (v/prove kb '(lkinOf Tib Rex))))
                   :conflicts   (count (v/conflicts kb))})
        result  (one-outcome-necessarily! "symmetric in the lead position" ops observe)]
    (testing "and the one outcome is the mirrored pair, forward and backward"
      (is (= '#{(lAlsoOwns Bob Rex)} (:conclusions result)))
      (is (true? (:proved result))
          "the mirror answers a goal, not only a join")
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

;; ---- a permuting mark, withdrawn ------------------------------------------
;;
;; A rule reaches a stored fact read the other way round through the fact's own permuting
;; mark — the join through the matcher's mirror, the trigger through `trigger-bindings`, a
;; rule arriving last through the full join — and each firing reached that way names the
;; mark (`chain/read-marks`).  So retracting the mark leaves what a KB that never held it
;; holds.  The mark is stated in a sibling, where the lift makes the CxUniverse copy the
;; supporter a firing names.

(defn- permuted-ops
  "The ops of a permuted firing: a rule on the fact alone, a join rule whose other
  antecedent binds the fact's second term, that antecedent's fact, the fact in its stored
  order, and each of `marks` — `{k [[mark & args] context]}` — stated of `pmRel` in its
  own sibling context, its handle into `h` under `k`."
  [marks h]
  ;; the siblings go in with the first rule, so a KB never told a mark still has them
  (into [#(do (doseq [cx '[CxPA CxPB]] (v/assert % (list 'genlCx cx 'CxUniverse) 'CxUniverse))
              (v/assert % '(implies (pmRel ?x ?y) (pmNoted ?x ?y)) 'CxUniverse {:direction :forward}))
         #(v/assert % '(implies (and (pmRel ?x ?y) (pm_tagged ?x)) (pmJoined ?x ?y))
                    'CxUniverse {:direction :forward})
         #(v/assert % '(pm_tagged Bea) 'CxUniverse)
         #(v/assert % '(pmRel Ada Bea) 'CxUniverse)]
        (for [[k [mark cx]] marks]
          #(swap! h assoc k (v/assert % (list* (first mark) 'pmRel (rest mark)) cx)))))

(defn- permuted-reading
  "The two mirrored conclusions and the stored one, at CxUniverse and at the sibling."
  [kb]
  (into {} (for [g '[(pmNoted Bea Ada) (pmJoined Bea Ada) (pmNoted Ada Bea)]
                 cx '[CxUniverse CxPA]]
             [[g cx] (v/ask? kb g cx)])))

(defn- a-permuting-mark-goes-with-the-mark
  "Each permuting mark licenses both mirrored firings, and retracting it leaves what a KB
  that never held it holds — over `cap` orderings of each scenario, or all of them."
  [cap]
  (doseq [mark '[[symmetric] [commutative] [commutativeInArgs 1 2] [commutativeInArgAndRest 1]]]
    (testing (str (first mark))
      (let [h        (atom {})
            never    (one-outcome! (str (first mark) ", never stated")
                                   (permuted-ops nil h) permuted-reading cap)
            held     (one-outcome! (str (first mark) ", held")
                                   (permuted-ops {:m [mark 'CxPA]} h) permuted-reading cap)
            retract  (one-outcome! (str (first mark) ", retracted")
                                   (permuted-ops {:m [mark 'CxPA]} h)
                                   (fn [kb] (v/retract! kb (:m @h)) (permuted-reading kb))
                                   cap)]
        (is (every? true? (vals held)) "the mark licenses both mirrored firings")
        (is (= [false false true] (mapv #(get never [% 'CxUniverse])
                                        '[(pmNoted Bea Ada) (pmJoined Bea Ada) (pmNoted Ada Bea)]))
            "without it only the stored order fires")
        (is (= never retract) "and retracting it leaves what a KB that never held it holds"))))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-firing-a-permuting-mark-licensed-goes-with-the-mark
  ;; a sample of each scenario's 24 or 120 orderings; the ^:slow twin walks every one
  (a-permuting-mark-goes-with-the-mark ordering-sample))

(deftest ^:slow every-ordering-of-a-firing-a-permuting-mark-licensed-goes-with-the-mark
  (a-permuting-mark-goes-with-the-mark nil))

(defn- two-permuting-marks-license
  "`(symmetric P)` and `(commutative P)` each license a binary fact's mirror, so the
  firing is one alternative per mark and the first retracted leaves it on the other —
  over `cap` of the 720 orderings, or all of them."
  [cap]
  (doseq [order [[:s :c] [:c :s]]]
    (testing (str "withdrawing " order)
      (let [h      (atom {})
            result (one-outcome! (str "two marks, withdrawing " order)
                                 (permuted-ops {:s ['[symmetric] 'CxPA] :c ['[commutative] 'CxPB]} h)
                                 (fn [kb]
                                   (vec (for [k (cons nil order)]
                                          (do (when k (v/retract! kb (get @h k)))
                                              (mapv #(v/ask? kb % 'CxUniverse)
                                                    '[(pmNoted Bea Ada) (pmJoined Bea Ada)])))))
                                 cap)]
        (is (= [[true true] [true true] [false false]] (vec result))))))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-firing-two-permuting-marks-license-survives-either-one
  ;; a sample of the 720 orderings; the ^:slow twin walks every one
  (two-permuting-marks-license ordering-sample))

(deftest ^:slow every-ordering-of-a-firing-two-permuting-marks-license-survives-either-one
  (two-permuting-marks-license nil))

;; ---- a bounded backward search ------------------------------------------

(deftest a-capped-proof-answers-the-same-whichever-rule-arrived-first
  ;; Three backward rules conclude one goal and each has its own witness, so a cap of one
  ;; answer is a *choice* among them.  The candidates come off the consequent index, whose
  ;; order is the handle order and so the assertion order, and **both** executors truncate
  ;; on that list: the DFS pushes a frame per candidate and `:max-results` stops it partway
  ;; through them, and the node engine fills its frontier from the same list and pops by an
  ;; estimate that ties three ways.  So the question is asked of both engines rather than
  ;; of whichever one the suite happens to be sweeping — a `binding` here, not
  ;; `tu/query-engine-override`, because this test drives the choice instead of standing
  ;; aside from it.
  (doseq [engine [:dfs :inference]]
    (binding [v/*query-engine* engine]
      (let [ops     [#(v/assert-rule % '[(p_src_a ?x)] '(p_reach ?x) 'CxUniverse
                                     {:direction :backward})
                     #(v/assert-rule % '[(p_src_b ?x)] '(p_reach ?x) 'CxUniverse
                                     {:direction :backward})
                     #(v/assert-rule % '[(p_src_c ?x)] '(p_reach ?x) 'CxUniverse
                                     {:direction :backward})
                     #(v/assert % '(p_src_a PrA) 'CxUniverse)
                     #(v/assert % '(p_src_b PrB) 'CxUniverse)
                     #(v/assert % '(p_src_c PrC) 'CxUniverse)]
            reached (fn [kb budget]
                      (into #{} (map #(get % '?x))
                            (:results (v/prove-within kb '(p_reach ?x) 'CxUniverse budget))))
            observe (fn [kb]
                      {:capped (reached kb {:max-results 1 :max-depth 3})
                       :whole  (reached kb {:max-depth 3})})
            result  (one-outcome-necessarily! (str "capped proof under " engine) ops observe 24)]
        (testing (str "and the reading is the sensible one under " engine)
          (is (= 1 (count (:capped result)))
              "a cap of one really is a choice among the three rules")
          (is (contains? (:whole result) (first (:capped result)))
              "and the answer it chose is one of the answers")
          (is (= '#{PrA PrB PrC} (:whole result))
              "while the uncapped run still reaches every witness")))))
  (tu/clear-kb! (tu/test-kb)))

;; ---- a generator's stamped rules -----------------------------------------

(deftest an-arity-declared-after-the-facts-names-the-same-facts-in-every-order
  ;; The declaration arrives in the reading, after every fact, so each ordering meets
  ;; the retroactive sweep rather than the entry-point refusal.  The entry names one
  ;; convicted fact and a sample of three out of four: a choice among them.
  (let [facts   '[(oiarity Aa Bb Cc) (oiarity Dd Ee Ff) (oiarity Gg Hh Ii) (oiarity Jj Kk Ll)]
        ops     (mapv (fn [f] #(v/assert % f 'CxUniverse)) facts)
        observe (fn [kb]
                  (v/clear-violations! kb)
                  (v/assert kb '(binary_predicate oiarity) 'CxUniverse)
                  (into [] (comp (filter #(= :arity (:violation %)))
                                 (map (juxt :sentence #(get-in % [:detail :sample]))))
                        (v/violations kb)))]
    (is (= [['(oiarity Aa Bb Cc) (vec (take 3 facts))]]
           (one-outcome! "the arity report" ops observe))))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-generator-and-its-stamped-rules-are-order-independent
  ;; The shape CxCore's arity vocabulary uses (docs/generators.md), stated over a
  ;; miniature so the scenario is the mechanism and not the ontology: one rule whose
  ;; consequent is itself a rule, a mapping fact that fills the hole, and members of the
  ;; type the hole names.  A stamped rule is minted when its mapping fact arrives and
  ;; may therefore arrive after the members it fires on, before them, or between two of
  ;; them.  120 orderings.
  (let [ops [#(v/assert % '(implies (typeArity ?type ?n)
                                    (implies (?type ?relation) (arity ?relation ?n)))
                        'CxUniverse {:direction :forward})
             #(v/assert % '(typeArity binary_thing 2) 'CxUniverse)
             #(v/assert % '(typeArity ternary_thing 3) 'CxUniverse)
             #(v/assert % '(binary_thing pairOf) 'CxUniverse)
             #(v/assert % '(ternary_thing tripleOf) 'CxUniverse)]
        observe (fn [kb]
                  {:pair   (boolean (seq (v/sentexes-matching kb '(arity pairOf 2) 'CxUniverse)))
                   :triple (boolean (seq (v/sentexes-matching kb '(arity tripleOf 3) 'CxUniverse)))
                   ;; the hole is filled per mapping fact, so one type's rule must not
                   ;; conclude for a member of the other
                   :crossed (boolean (seq (v/sentexes-matching kb '(arity pairOf 3) 'CxUniverse)))
                   :rows    (count (v/sentexes-matching kb '(arity ?r ?n) 'CxUniverse))
                   :conflicts (count (v/conflicts kb))})
        result (one-outcome-necessarily! "generator stamping" ops observe)]
    (testing "and the one reading is one arity per member, from its own type's rule"
      (is (true? (:pair result)))
      (is (true? (:triple result)))
      (is (false? (:crossed result)))
      (is (= 2 (:rows result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest withdrawing-a-generators-premise-is-order-independent
  ;; The withdrawal half.  A stamped rule is justified by the fact that minted it, so
  ;; retracting the fact must take the rule's conclusions with it and leave every other
  ;; type's alone — whenever in the sequence the retraction lands.  The retract names the
  ;; handle its own assert allocated, so the two are one chain; 5!/2! = 60 orderings.
  (let [handle (volatile! nil)
        chains [[#(v/assert % '(implies (typeArity ?type ?n)
                                        (implies (?type ?relation) (arity ?relation ?n)))
                            'CxUniverse {:direction :forward})]
                [#(vreset! handle (v/assert % '(typeArity binary_thing 2) 'CxUniverse))
                 #(v/retract! % @handle)]
                [#(v/assert % '(typeArity ternary_thing 3) 'CxUniverse)]
                [#(v/assert % '(binary_thing pairOf) 'CxUniverse)]
                [#(v/assert % '(ternary_thing tripleOf) 'CxUniverse)]]
        observe (fn [kb]
                  {:pair    (boolean (seq (v/sentexes-matching kb '(arity pairOf 2) 'CxUniverse)))
                   :triple  (boolean (seq (v/sentexes-matching kb '(arity tripleOf 3) 'CxUniverse)))
                   :member  (boolean (seq (v/sentexes-matching kb '(binary_thing pairOf) 'CxUniverse)))
                   :mapping (boolean (seq (v/sentexes-matching kb '(typeArity binary_thing 2)
                                                               'CxUniverse)))
                   :rows    (count (v/sentexes-matching kb '(arity ?r ?n) 'CxUniverse))
                   :conflicts (count (v/conflicts kb))})
        result (one-outcome-under! "generator withdrawal" chains observe)]
    (testing "the withdrawn fact takes its own conclusion and nothing else"
      (is (false? (:pair result)) "the stamped rule's conclusion goes with its premise")
      (is (false? (:mapping result)))
      (is (true? (:member result)) "the membership was asserted and stands on its own")
      (is (true? (:triple result)) "the other type's rule is untouched")
      (is (= 1 (:rows result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

;; ---- the entry point's refusal ------------------------------------------

(defn- lattice-kb
  "A KB under an explicit constraint policy, for the lattice below.  The policy has to be
  the KB's own rather than the process default, because the two answers being compared
  are what each policy does with the same three sentences.

  Cleared on open, as `tu/fresh` is: the namespace has no fixture, so the scratch space
  holds whatever the namespace before it left there, and a KB opened over records it
  never settled refuses every write as `:unrecovered-kb`."
  [policy]
  (fn [] (doto (v/open-kb (assoc tu/scratch-space :constraints policy)) (tu/clear-kb!))))

(defn- lattice-cell!
  "Write the three sentences of CxB in `order` into a fresh lattice, catching the entry
  point's refusal, and read back what the KB holds and believes.

  The lattice is prompt 03's and prompt 08's:

      CxUniverse   (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
       └─ CxA      (genl chi dog)                 :default
            └─ CxB (not (genl chi dog))           :monotonic
                   (chi Kit)  (cat Kit)

  CxB disbelieves the edge, so from CxB `chi` is not a `dog` and the two memberships of
  `Kit` clash with nothing.  Everything above CxA is known-true; the one defeasible
  ingredient is the edge, which is what the denial withdraws."
  [policy cat-strength order]
  (tu/with-neutral-kb [kb (lattice-kb policy)]
    (tu/with-terms [CxA CxB chi_t dog_t cat_t Kit]
      (doseq [t [chi_t dog_t cat_t]]
        (v/assert kb (list 'genl t 'thing) 'CxUniverse {:strength :monotonic}))
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl chi_t dog_t) CxA)
      (let [refused (atom 0)
            write!  {:chi    #(v/assert kb (list chi_t Kit) CxB)
                     :cat    #(v/assert kb (list cat_t Kit) CxB {:strength cat-strength})
                     :denial #(v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB
                                        {:strength :monotonic})}]
        (doseq [k order]
          (try ((write! k)) (catch clojure.lang.ExceptionInfo _ (swap! refused inc))))
        {:refused @refused
         :stored  (count (filter some?
                                 [(v/handle-of kb (list chi_t Kit) CxB)
                                  (v/handle-of kb (list cat_t Kit) CxB)
                                  (v/handle-of kb (list 'not (list 'genl chi_t dog_t)) CxB)]))
         :chi?    (v/ask? kb (list chi_t Kit) CxB)
         :cat?    (v/ask? kb (list cat_t Kit) CxB)
         :contra  (count (v/contradictions kb))}))))

(def ^:private lattice-orders
  (into [] (permutations [:chi :cat :denial])))

(deftest a-definitional-refusal-does-not-follow-the-write-order
  ;; Six write orders, both strengths of `(cat Kit)`, under `:arbitrate`.  At the moment
  ;; `(chi Kit)` is offered in two of them, CxB still reads the separation and
  ;; `(cat Kit)` may be known-true — so the entry point once threw the sentence away, and
  ;; the other four orders stored and believed it.  A refusal that turns on which
  ;; sentence arrived first is a refusal the writer cannot predict and the reader cannot
  ;; explain.
  ;;
  ;; The separation is **derived**: it reaches `chi` over the `:default` `(genl chi dog)`
  ;; edge in CxA, and the denial in CxB takes that edge out of CxB's view.  So the pair
  ;; is one the KB can be told otherwise about, `checks/grounds-class` reads it as
  ;; `:default`, and the sentence is admitted and weighed instead of refused.  One
  ;; outcome, all six orders, both strengths.
  (doseq [cat-strength [:monotonic :default]]
    (testing (str "(cat Kit) " cat-strength)
      (let [readings (mapv #(lattice-cell! :arbitrate cat-strength %) lattice-orders)]
        (is (= 1 (count (distinct readings)))
            (str "one reading over six orders — " (pr-str (frequencies readings))))
        (let [r (first readings)]
          (is (zero? (:refused r)) "nothing is turned away in any order")
          (is (= 3 (:stored r))    "and all three sentences are held")
          (is (true? (:chi? r)))
          (is (true? (:cat? r))    "both memberships stand at CxB")
          (is (zero? (:contra r))  "and no pair is reported to a reader that reads none")))))
  (tu/clear-kb! (tu/test-kb)))

(deftest under-refuse-the-writer-is-told-no-and-that-does-follow-the-order
  ;; The case the invariant does **not** cover, stated rather than left to be discovered.
  ;; `:refuse` is a policy about whether a *writer* is told no (`checks/arbitrating?`),
  ;; and a writer is answered from the KB in front of it — so the two orders that offer a
  ;; membership while CxB still reads the separation are refused, and the four that do
  ;; not are stored.  The engine-wide invariant is over **beliefs** (docs/nmtms.md,
  ;; "1. Order independence"), and every order that stores agrees about those.
  (doseq [cat-strength [:monotonic :default]]
    (testing (str "(cat Kit) " cat-strength)
      (let [readings (mapv #(lattice-cell! :refuse cat-strength %) lattice-orders)
            stored   (filterv #(zero? (:refused %)) readings)]
        (is (= 4 (count stored)) "four of six orders store the three sentences")
        (is (= 1 (count (distinct stored)))
            (str "and they agree about everything — " (pr-str (frequencies stored))))
        (is (every? #(and (true? (:chi? %)) (true? (:cat? %)) (zero? (:contra %))) stored)
            "both memberships stand at CxB, and nothing is reported")
        (testing "the two that refuse are the ones offering a membership before the denial"
          (is (= [[:chi :cat :denial] [:cat :chi :denial]]
                 (mapv first (filterv (fn [[_ r]] (pos? (:refused r)))
                                      (mapv vector lattice-orders readings))))))))
    (tu/clear-kb! (tu/test-kb))))
