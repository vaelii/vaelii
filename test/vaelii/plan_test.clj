;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.plan-test
  "Conjunctive query planning (`vaelii.impl.plan`).

  The planner reorders a conjunction for cost, so the two things worth testing are
  that it *does* reorder — the selective literal ends up first however the caller
  wrote it — and that reordering is invisible in the answers.  The second is the one
  that matters: an ordering bug does not throw, it silently returns a different
  answer set, and for a hoisted `evaluate` it silently returns *none*."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (vec coll))
    (for [i (range (count coll))
          p (permutations (concat (subvec (vec coll) 0 i) (subvec (vec coll) (inc i))))]
      (into [(nth coll i)] p))))

(defn- unplanned
  "Run `f` with the planner inert, for comparison against the planned run."
  [f]
  (binding [plan/*enabled* false] (f)))

;; ---- the cost model -----------------------------------------------------

(tu/deftest-kb a-ground-argument-makes-a-literal-cheaper
  (tu/with-terms [parentOf Tom Bob Ann Cid PlanContext]
    (doseq [[p c] [[Tom Bob] [Tom Ann] [Bob Cid] [Ann Cid]]]
      (v/assert kb (list parentOf p c) PlanContext))
    (testing "the trie counts the ground prefix exactly; the open literal is the extent"
      (is (= 2 (plan/est-matches kb (list parentOf Tom '?y) #{})))
      (is (= 4 (plan/est-matches kb (list parentOf '?x '?y) #{}))))
    (testing "a fully ground literal is a test — it matches at most once"
      (is (= 1 (plan/est-matches kb (list parentOf Tom Bob) #{}))))))

(tu/deftest-kb a-bound-variable-makes-a-literal-cheaper
  (tu/with-terms [parentOf Tom Bob Ann Cid PlanContext]
    (doseq [[p c] [[Tom Bob] [Tom Ann] [Bob Cid] [Ann Cid]]]
      (v/assert kb (list parentOf p c) PlanContext))
    (testing "sideways information passing: the same literal costs less once ?x is bound"
      (let [open  (plan/est-matches kb (list parentOf '?x '?y) #{})
            bound (plan/est-matches kb (list parentOf '?x '?y) '#{?x})]
        (is (< bound open))))
    (testing "and a literal with everything bound is a test"
      (is (= 1 (plan/est-matches kb (list parentOf '?x '?y) '#{?x ?y}))))))

(tu/deftest-kb a-supertype-literal-costs-its-whole-subtree
  (tu/with-terms [animal dog cat Muffet Tom PlanContext]
    (v/assert kb (list 'genl dog animal) PlanContext)
    (v/assert kb (list 'genl cat animal) PlanContext)
    (v/assert kb (list dog Muffet) PlanContext)
    (v/assert kb (list cat Tom) PlanContext)
    (testing "matching fans out over the subtype closure, so the supertype is dearer"
      ;; `animal` has no instance of its own — costing it by its own extent would
      ;; rank the most expensive literal in the conjunction as the cheapest
      (is (> (plan/est-matches kb (list animal '?x) #{})
             (plan/est-matches kb (list dog '?x) #{}))))))

(tu/deftest-kb an-open-functor-is-costed-by-the-argument-root
  ;; `(?type Muffet)` names no predicate, so neither functor-keyed model applies: there
  ;; is no subtype closure to fan and no functor root to count.  The matcher answers it
  ;; from the position-1 argument roots (a slot-roster union), so the estimate has to be
  ;; that same count — costing it by the trie (which stops dead at the open first token)
  ;; charges the whole KB.
  (tu/with-terms [animal dog Muffet Other PlanContext]
    (v/assert kb (list 'genl dog animal) PlanContext)
    (v/assert kb (list dog Muffet) PlanContext)
    (v/assert kb (list animal Other) PlanContext)
    (testing "bounded by the argument root, not by the size of the KB"
      (is (= (p/count-with-arg (:index kb) 1 Muffet)
             (plan/est-matches kb (list '?c Muffet) #{}))))
    (testing "with nothing indexable to lead with, nothing bounds it"
      (is (< (plan/est-matches kb (list '?c Muffet) #{})
             (plan/est-matches kb '(?c ?x) #{}))))
    (testing "a concrete unary functor still fans over its subtype closure"
      (is (> (plan/est-matches kb (list animal '?x) #{})
             (plan/est-matches kb (list dog '?x) #{}))))
    (testing "a negated open functor is not ranked cheapest"
      ;; the functor root answers 0 for a variable — a *lower* bound, which would hoist
      ;; the dearest literal in the conjunction to the front
      (is (pos? (plan/est-matches kb (list 'not (list '?c Muffet)) #{}))))))

(tu/deftest-kb a-dotted-rest-pattern-is-not-ranked-free
  ;; `(rel . ?args)` splices a whole argument list, so no argument sits at a position
  ;; the trie key or an argument root pins, and the marker itself is not a term —
  ;; both models answer 0 for it, which would rank the literal cheapest and hoist a
  ;; whole extent to the front of the conjunction.
  (tu/with-terms [rel dog Tom Bob Rex PlanContext]
    (doseq [[a b] [[Tom Bob] [Bob Tom]]] (v/assert kb (list rel a b) PlanContext))
    (v/assert kb (list dog Rex) PlanContext)
    (testing "a concrete functor is bounded by its extent, exactly as the fixed-arity form is"
      (is (= (plan/est-matches kb (list rel '?x '?y) #{})
             (plan/est-matches kb (list rel '. '?args) #{}))))
    (testing "an open functor with a dotted rest is bounded by nothing"
      (is (> (plan/est-matches kb (list '?p '. '?args) #{})
             (plan/est-matches kb (list rel '. '?args) #{}))))
    (testing "negated, the marker must not floor the estimate either"
      ;; the negative arm reaches the argument roots for an open functor, so a dotted
      ;; body would ask them about `.` and get 0 back
      (is (pos? (plan/est-matches kb (list 'not (list '?p '. '?args)) #{})))
      (is (pos? (plan/est-matches kb (list 'not (list rel '. '?args)) #{}))))
    (testing "so the selective literal still leads, whichever way it was written"
      (let [dotted (list rel '. '?args)
            sel    (list dog '?x)]
        (is (= [sel dotted] (plan/order kb [dotted sel] PlanContext)))
        (is (= [sel dotted] (plan/order kb [sel dotted] PlanContext)))))))

;; ---- ordering -----------------------------------------------------------

(tu/deftest-kb an-open-functor-leads-when-it-is-the-selective-literal
  (tu/with-terms [animal dog cat bird Muffet PlanContext]
    ;; a type hierarchy wide enough that walking it is dearer than reading Muffet's
    ;; own memberships, which is the whole point of leading with the latter
    (doseq [t [dog cat bird]] (v/assert kb (list 'genl t animal) PlanContext))
    (v/assert kb (list dog Muffet) PlanContext)
    (let [open   (list '?c Muffet)
          hier   (list 'genl '?c animal)
          answers (fn [gs] (set (map #(get % '?c) (v/prove kb gs PlanContext))))]
      (testing "written either way, the open functor is picked first"
        (is (= [open hier] (plan/order kb [open hier] PlanContext)))
        (is (= [open hier] (plan/order kb [hier open] PlanContext))))
      (testing "and the reordering changes no answers"
        (let [expected (unplanned #(answers [open hier]))]
          (is (seq expected))
          (is (= expected (answers [open hier])))
          (is (= expected (answers [hier open])))
          (is (= expected (unplanned #(answers [hier open])))))))))

(tu/deftest-kb the-selective-literal-goes-first-however-it-was-written
  (tu/with-terms [parentOf dog Tom Bob Ann Cid PlanContext]
    (doseq [[p c] [[Tom Bob] [Bob Cid] [Ann Cid]]]
      (v/assert kb (list parentOf p c) PlanContext))
    (doseq [d [Bob Cid Ann]] (v/assert kb (list dog d) PlanContext))
    (let [selective (list parentOf Tom '?y)
          general   (list dog '?y)]
      (testing "written selective-first, it stays first"
        (is (= [selective general] (plan/order kb [selective general] PlanContext))))
      (testing "written general-first, the planner swaps it"
        (is (= [selective general] (plan/order kb [general selective] PlanContext)))))))

(tu/deftest-kb planning-is-deterministic-and-breaks-ties-on-written-order
  (tu/with-terms [likes Tom Bob PlanContext]
    (v/assert kb (list likes Tom Bob) PlanContext)
    (let [a (list likes '?x '?y)
          b (list likes '?y '?z)
          conj- [a b]]
      (testing "the same conjunction plans the same way every time"
        (is (apply = (repeatedly 5 #(plan/order kb conj- PlanContext)))))
      (testing "equal-cost literals keep the order they were written in"
        (is (= a (first (plan/order kb [a b] PlanContext))))))))

(tu/deftest-kb a-repeated-conjunct-is-not-dropped
  (tu/with-terms [parentOf Tom Bob PlanContext]
    (v/assert kb (list parentOf Tom Bob) PlanContext)
    (testing "planning is a permutation — it never shortens the conjunction"
      (let [g (list parentOf '?x '?y)]
        (is (= 3 (count (plan/order kb [g g g] PlanContext))))))))

;; ---- costing the plan, not the next literal -----------------------------

(defn- chain-kb!
  "A 1:1 chain `link1 ?a ?b`, `link2 ?b ?c`, `link3 ?c ?d` of `n` facts each, plus a
  `loose` relation of `few` facts sharing no variable with them.

  This is the shape a per-literal cost model gets wrong.  `loose` is the smallest
  extent in the KB and constrains nothing, so taking the cheapest literal available
  puts it *first*, where it multiplies every row count after it; the chain literals
  look dearer alone and each collapses to one row once its join variable is bound."
  [kb ctx [link1 link2 link3 loose Node] n few]
  (let [node (fn [p i] (symbol (str Node p i)))]
    (v/assert-many kb
                   (concat (for [i (range n)] (list link1 (node "A" i) (node "B" i)))
                           (for [i (range n)] (list link2 (node "B" i) (node "C" i)))
                           (for [i (range n)] (list link3 (node "C" i) (node "D" i)))
                           (for [i (range few)] (list loose (node "U" i) (node "V" i))))
                   ctx {:chain? false})))

(defn- actual-rows
  "Σ of the partial-solution counts an order passes through — what running it costs.

  Measured with the engine rather than modelled: the *k*-th intermediate is the
  solution count of the order's first *k* literals, which is what a prefix query
  returns.  A solution count is a property of the literal set and not of its
  arrangement, so this reads the same whoever ordered the prefix."
  [kb order ctx]
  (reduce + (for [k (range 1 (inc (count order)))]
              (unplanned #(count (v/prove kb (vec (take k order)) ctx))))))

(tu/deftest-kb a-literal-that-binds-nothing-goes-last-however-cheap-it-is
  (tu/with-terms [linkOne linkTwo linkThree loose Node PlanContext]
    (chain-kb! kb PlanContext [linkOne linkTwo linkThree loose Node] 6 3)
    (let [c1      (list linkOne '?a '?b)
          c2      (list linkTwo '?b '?c)
          c3      (list linkThree '?c '?d)
          lo      (list loose '?u '?v)
          written [lo c1 c2 c3]]
      (testing "`loose` really is the cheapest literal taken on its own"
        (is (< (plan/est-matches kb lo #{}) (plan/est-matches kb c1 #{}))))
      (testing "and it is still planned last, because its bindings buy nothing"
        (is (= [c1 c2 c3 lo] (plan/order kb written PlanContext))))
      (testing "which is the order with the fewest intermediate rows"
        (is (= (actual-rows kb [c1 c2 c3 lo] PlanContext)
               (apply min (map #(actual-rows kb % PlanContext)
                               (permutations written))))))
      (testing "and the plan reports *why* it is last, not just a small estimate there"
        (let [rows (plan/explain kb written PlanContext)]
          (is (= [lo] (map :goal (filter :isolated? rows))))
          ;; the trap the flag exists for: it is the cheapest literal in the
          ;; conjunction and sits last, which without a reason reads as a mistake
          (is (:isolated? (last rows)))
          (is (< (:est-matches (last rows)) (:est-matches (first rows)))))))))

(tu/deftest-kb at-two-literals-the-cheaper-one-leads-and-that-is-already-optimal
  ;; Two is the common width — a rule's antecedents — and the width at which costing
  ;; the plan and costing the next literal provably agree: both orders end on the same
  ;; join, so the costs differ only by the leading literal's own extent.  Pinned
  ;; because it is why the search is not run here, not merely why it need not be.
  (tu/with-terms [linkOne linkTwo linkThree loose Node PlanContext]
    (chain-kb! kb PlanContext [linkOne linkTwo linkThree loose Node] 6 3)
    (let [c1 (list linkOne '?a '?b)
          lo (list loose '?u '?v)]
      (testing "the cheaper literal leads, written either way"
        (is (< (plan/est-matches kb lo #{}) (plan/est-matches kb c1 #{})))
        (is (= [lo c1] (plan/order kb [lo c1] PlanContext)))
        (is (= [lo c1] (plan/order kb [c1 lo] PlanContext))))
      (testing "and no permutation of the pair runs fewer rows"
        (is (= (actual-rows kb [lo c1] PlanContext)
               (min (actual-rows kb [lo c1] PlanContext)
                    (actual-rows kb [c1 lo] PlanContext))))))))

(tu/deftest-kb the-planned-order-is-the-cheapest-of-every-permutation
  (tu/with-terms [linkOne linkTwo linkThree loose Node PlanContext]
    (chain-kb! kb PlanContext [linkOne linkTwo linkThree loose Node] 5 2)
    (let [conjuncts [(list loose '?u '?v)
                     (list linkOne '?a '?b)
                     (list linkTwo '?b '?c)
                     (list linkThree '?c '?d)]]
      (testing "the search is exact, not merely better: no permutation runs fewer rows"
        (let [planned (plan/order kb conjuncts PlanContext)
              costs   (map #(actual-rows kb % PlanContext) (permutations conjuncts))]
          (is (= (actual-rows kb planned PlanContext) (apply min costs)))))
      (testing "and the cartesian factor is last however the conjunction was written"
        ;; the connected head may still differ between permutations — those literals
        ;; have equal extents, and a cost tie resolves to written order by design
        (doseq [p (permutations conjuncts)]
          (is (= (list loose '?u '?v) (last (plan/order kb p PlanContext)))))))))

(defn- random-trial!
  "One randomized join: four relations over a shared pool of individuals, and a
  conjunction of one literal each whose variables are drawn from a pool small enough
  that some literals share and some do not.  Returns the conjunction.

  Relations are named per trial so trials do not see each other's facts, and every
  name derives from the caller's gensym'd bases, so the fixture still retracts the
  lot."
  [kb ctx rel-base node-base ^java.util.Random rng trial]
  (let [rel  (fn [i] (symbol (str rel-base "t" trial "x" i)))
        node (fn [i] (symbol (str node-base "N" i)))
        pool 6
        vars '[?p ?q ?r ?s]]
    (v/assert-many kb
                   (for [i (range 4)
                         _ (range (+ 2 (.nextInt rng 5)))]
                     (list (rel i) (node (.nextInt rng pool)) (node (.nextInt rng pool))))
                   ctx {:chain? false})
    (mapv (fn [i] (list (rel i)
                        (nth vars (.nextInt rng (count vars)))
                        (nth vars (.nextInt rng (count vars)))))
          (range 4))))

(defn- isolated-literals
  "The conjuncts sharing no variable with any other conjunct *and* carrying a variable
  to share — what the planner holds to the back, restated here so the test computes it
  rather than trusting it.

  The second clause is not pedantry.  `every?` over an empty sequence is true, so a
  conjunct with no variables at all satisfies the sharing test vacuously — and a
  ground conjunct is a one-lookup test that belongs *first*, the opposite of what
  being held back would do to it.  `random-trial!` gives every conjunct two variables
  and several facts, so no trial reaches either edge; the deterministic tests below
  are what cover them."
  [conjuncts]
  (let [vars  (fn [l] (set (filter #(and (symbol? %) (.startsWith (name %) "?"))
                                   (tree-seq sequential? seq l))))
        counts (frequencies (mapcat (comp seq vars) conjuncts))]
    (set (filter #(and (seq (vars %))
                       (every? (fn [v] (= 1 (counts v))) (vars %)))
                 conjuncts))))

(tu/deftest-kb ^:slow every-cartesian-factor-runs-after-every-connected-literal
  ;; The placement rule is structural, so a randomized shape can check it exactly
  ;; rather than within a factor.  Estimate *quality* is a separate question this
  ;; deliberately does not assert: the index bounds a literal from above, those
  ;; bounds do not compose across a join, and a plan is not claimed to be optimal.
  (tu/with-terms [rel Node PlanContext]
    (let [rng    (java.util.Random. 20260730)
          trials (for [trial (range 12)]
                   (let [conjuncts (random-trial! kb PlanContext rel Node rng trial)]
                     {:conjuncts conjuncts
                      :planned   (plan/order kb conjuncts PlanContext)
                      :isolated  (isolated-literals conjuncts)}))
          witnessed (filter #(seq (:isolated %)) trials)]
      (testing "the trials threw up cartesian factors to place at all"
        (is (seq witnessed)))
      (testing "each one runs after every literal that is not one"
        (doseq [{:keys [planned isolated]} witnessed]
          (let [last-connected (->> planned
                                    (keep-indexed (fn [i l] (when-not (isolated l) i)))
                                    (reduce max -1))
                first-isolated (->> planned
                                    (keep-indexed (fn [i l] (when (isolated l) i)))
                                    (reduce min Long/MAX_VALUE))]
            (is (< last-connected first-isolated)
                (str "plan " (pr-str planned) " isolated " (pr-str isolated))))))
      (testing "and planning still changes no answers, whatever it reordered"
        (doseq [{:keys [conjuncts planned]} trials]
          (let [answers (fn [gs] (set (v/prove kb gs PlanContext)))]
            (is (= (unplanned #(answers conjuncts)) (answers planned)))))))))

(defn- fan-kb!
  "A chain of `linkOne`/`linkTwo` that fans out — 20 rows joining to 80 — so an
  ordering mistake in front of it is paid 80 times rather than once."
  [kb ctx linkOne linkTwo Node]
  (v/assert-many kb
                 (concat (for [i (range 20)]
                           (list linkOne (symbol (str Node "A" i))
                                 (symbol (str Node "B" (mod i 5)))))
                         (for [j (range 5), k (range 4)]
                           (list linkTwo (symbol (str Node "B" j))
                                 (symbol (str Node "C" k)))))
                 ctx {:chain? false}))

(tu/deftest-kb a-ground-literal-is-a-test-and-leads-rather-than-being-deferred
  ;; The trap in the placement rule, and the shape both chaining paths hand the
  ;; planner: antecedents are substituted with the trigger's bindings *before*
  ;; planning (`chain/planned-join`, `res/planned-antecedents`), so an antecedent whose
  ;; variables the trigger bound arrives here fully ground.  A ground literal shares no
  ;; variable with anything — it has none — so the structural test passes it vacuously,
  ;; and holding it back runs the entire join before the one lookup that refutes it.
  (tu/with-terms [linkOne linkTwo guard Node PlanContext]
    (fan-kb! kb PlanContext linkOne linkTwo Node)
    (let [g       (list guard (symbol (str Node "Zed")))   ; asserted nowhere: no match
          c1      (list linkOne '?a '?b)
          c2      (list linkTwo '?b '?c)
          written [c1 c2 g]]
      (testing "it is the cheapest literal present, and soundly so — a test matches once"
        (is (= 1 (plan/est-matches kb g #{}))))
      (testing "so it leads, and the join behind it is never run"
        (is (= [g c1 c2] (plan/order kb written PlanContext)))
        (is (zero? (actual-rows kb [g c1 c2] PlanContext)))
        (is (pos? (actual-rows kb [c1 c2 g] PlanContext))))
      (testing "which is the order with the fewest intermediate rows"
        (is (= (actual-rows kb [g c1 c2] PlanContext)
               (apply min (map #(actual-rows kb % PlanContext)
                               (permutations written))))))
      (testing "and the plan does not claim it was held back as a cartesian factor"
        (is (not-any? :isolated? (plan/explain kb written PlanContext)))))))

(tu/deftest-kb an-unshared-literal-that-cannot-fan-out-leads-too
  ;; The same rule stated over an estimate rather than over structure.  `loose` shares
  ;; no variable, but one fact matches it, so it multiplies by one: it cannot fan the
  ;; plan out, only sit in it.  `est-matches` bounds from above, so an estimate of 1
  ;; *proves* that — the one direction the bound is sound in.
  (tu/with-terms [linkOne linkTwo loose Node PlanContext]
    (fan-kb! kb PlanContext linkOne linkTwo Node)
    (v/assert kb (list loose (symbol (str Node "U0")) (symbol (str Node "V0"))) PlanContext)
    (let [lo      (list loose '?u '?v)
          c1      (list linkOne '?a '?b)
          c2      (list linkTwo '?b '?c)
          written [c1 c2 lo]]
      (is (= 1 (plan/est-matches kb lo #{})))
      (testing "it leads, and running it last would cost strictly more"
        (is (= [lo c1 c2] (plan/order kb written PlanContext)))
        (is (< (actual-rows kb [lo c1 c2] PlanContext)
               (actual-rows kb [c1 c2 lo] PlanContext))))
      (testing "and a second fact makes it a multiplier, which is held back as before"
        (v/assert kb (list loose (symbol (str Node "U1")) (symbol (str Node "V1")))
                  PlanContext)
        (is (= [c1 c2 lo] (plan/order kb written PlanContext)))
        (is (= [lo] (map :goal (filter :isolated? (plan/explain kb written PlanContext)))))))))

(tu/deftest-kb a-literal-feeding-an-evaluable-is-not-a-cartesian-factor
  ;; `age` shares no variable with either chain literal, so read against the
  ;; generators alone it looks isolated and would be held to the back — taking the
  ;; evaluable that consumes its binding with it, and costing the run the early prune
  ;; that evaluable exists to give.  Sharing is therefore judged against every literal
  ;; the caller wrote, the deferred ones included.  Nothing else in this namespace
  ;; fails if that widening is dropped.
  (tu/with-terms [linkOne linkTwo age Person Node PlanContext]
    (doseq [i (range 6)]
      (v/assert kb (list linkOne (symbol (str Node "A" i)) (symbol (str Node "B" i))) PlanContext)
      (v/assert kb (list linkTwo (symbol (str Node "B" i)) (symbol (str Node "C" i))) PlanContext))
    (v/assert kb (list age (symbol (str Person "One")) 30) PlanContext)
    (v/assert kb (list age (symbol (str Person "Two")) 40) PlanContext)
    (let [ordered (plan/order kb [(list linkOne '?a '?b)
                                  (list linkTwo '?b '?c)
                                  (list age '?p '?n)
                                  (list 'lessThan '?n 35)]
                              PlanContext)]
      (testing "it leads on its own cost, rather than being deferred as isolated"
        (is (= (list age '?p '?n) (first ordered))))
      (testing "so the evaluable it binds is pulled forward behind it, and prunes early"
        (is (= 'lessThan (first (second ordered)))))
      (testing "and the plan says so: nothing here is reported as a cartesian factor"
        (is (not-any? :isolated? (plan/explain kb [(list linkOne '?a '?b)
                                                   (list linkTwo '?b '?c)
                                                   (list age '?p '?n)
                                                   (list 'lessThan '?n 35)]
                                               PlanContext)))))))

;; ---- what must never be reordered ---------------------------------------

(tu/deftest-kb a-deferred-literal-never-outruns-what-binds-it
  (tu/with-terms [age Tom Bob PlanContext]
    (v/assert kb (list age Tom 30) PlanContext)
    (v/assert kb (list age Bob 40) PlanContext)
    (testing "an evaluable stays behind the literal binding its arguments"
      (let [ordered (plan/order kb [(list 'lessThan '?n 35) (list age '?p '?n)] PlanContext)]
        (is (= age (first (first ordered))))
        (is (= 'lessThan (first (second ordered))))))
    (testing "so does an evaluate — hoisting one yields no solutions rather than an error"
      (let [ordered (plan/order kb [(list 'evaluate '?z (list '+ '?n 1)) (list age '?p '?n)]
                                PlanContext)]
        (is (= age (first (first ordered))))))))

(tu/deftest-kb a-deferred-literal-is-pulled-forward-once-its-variables-are-bound
  (tu/with-terms [age likes Tom Bob PlanContext]
    (v/assert kb (list age Tom 30) PlanContext)
    (v/assert kb (list likes Tom Bob) PlanContext)
    (testing "a test that can run early prunes early — it does not sit uniformly last"
      (let [ordered (plan/order kb [(list age '?p '?n)
                                    (list 'lessThan '?n 35)
                                    (list likes '?p '?q)]
                                PlanContext)]
        ;; the filter on ?n belongs directly after the literal that binds ?n, not
        ;; after the unrelated `likes` join it would otherwise multiply through
        (is (= 'lessThan (first (nth ordered 1))))))))

(tu/deftest-kb the-recursive-literal-stays-last-so-recursion-still-terminates
  (tu/with-terms [parentOf ancestorOf Aa Bb Cc Dd PlanContext]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) PlanContext)
    (v/assert-rule kb [(list parentOf '?x '?y) (list ancestorOf '?y '?z)]
                   (list ancestorOf '?x '?z) PlanContext)
    (doseq [[p c] [[Aa Bb] [Bb Cc] [Cc Dd]]]
      (v/assert kb (list parentOf p c) PlanContext))
    (testing "the literal sharing the consequent's functor is pinned last"
      (let [ordered (plan/order kb [(list ancestorOf '?y '?z) (list parentOf '?x '?y)]
                                PlanContext {:consequent-pred ancestorOf})]
        (is (= parentOf   (first (first ordered))))
        (is (= ancestorOf (first (second ordered))))))
    (testing "so a right-recursive rule still terminates and closes transitively"
      (is (= #{Bb Cc Dd}
             (set (map #(get % '?who)
                       (v/prove kb (list ancestorOf Aa '?who) PlanContext))))))))

;; ---- the invariant: cost changes, meaning does not -----------------------

(tu/deftest-kb planning-never-changes-the-answer-set
  (tu/with-terms [parentOf dog cat Tom Bob Ann Cid PlanContext]
    (doseq [[p c] [[Tom Bob] [Tom Ann] [Bob Cid] [Ann Cid]]]
      (v/assert kb (list parentOf p c) PlanContext))
    (v/assert kb (list dog Bob) PlanContext)
    (v/assert kb (list dog Cid) PlanContext)
    (v/assert kb (list cat Ann) PlanContext)
    (let [conjuncts [(list parentOf Tom '?y) (list dog '?y) (list parentOf '?y '?z)]
          answers   (fn [gs] (set (map #(select-keys % '[?y ?z]) (v/prove kb gs PlanContext))))
          expected  (unplanned #(answers conjuncts))]
      (testing "the query has answers at all — otherwise this proves nothing"
        (is (seq expected)))
      (testing "every permutation, planned, gives exactly the unplanned answer set"
        (doseq [p (permutations conjuncts)]
          (is (= expected (answers p)) (str "permutation " (pr-str p)))
          (is (= expected (unplanned #(answers p))) (str "unplanned " (pr-str p))))))))

(tu/deftest-kb planning-never-changes-the-answer-set-through-a-rule
  (tu/with-terms [parentOf grandparentOf dog Tom Bob Ann Cid PlanContext]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) PlanContext)
    (doseq [[p c] [[Tom Bob] [Bob Cid] [Tom Ann] [Ann Cid]]]
      (v/assert kb (list parentOf p c) PlanContext))
    (v/assert kb (list dog Cid) PlanContext)
    (let [goal    [(list grandparentOf Tom '?z) (list dog '?z)]
          answers (fn [gs] (set (map #(get % '?z) (v/prove kb gs PlanContext))))]
      (testing "a planned rule expansion agrees with an unplanned one"
        (is (= #{Cid} (answers goal)))
        (is (= (unplanned #(answers goal)) (answers goal))))
      (testing "and so does the reversed conjunction"
        (is (= (answers goal) (answers (vec (reverse goal)))))))))

(tu/deftest-kb an-evaluable-antecedent-still-computes-under-planning
  ;; An evaluable is reachable through the *prover* stack, so the conjunction that
  ;; exercises it is a rule's antecedents (planned by `provers/planned-antecedents`)
  ;; rather than a `prove` goal vector — see the limitation pinned below.
  (tu/with-terms [age young Tom Bob Cid PlanContext]
    (v/assert kb (list age Tom 30) PlanContext)
    (v/assert kb (list age Bob 40) PlanContext)
    (v/assert kb (list age Cid 20) PlanContext)
    (v/assert-rule kb [(list age '?p '?n) (list 'lessThan '?n 35)]
                   (list young '?p) PlanContext)
    (let [answers (fn [] (set (map #(get % '?p) (v/ask kb (list young '?p) PlanContext))))]
      (testing "the filter applies — a hoisted evaluable would silently answer none"
        (is (= #{Tom Cid} (answers))))
      (testing "and the planned run agrees with the unplanned one"
        (is (= (unplanned answers) (answers)))))))

(tu/deftest-kb prove-evaluates-an-evaluable-conjunct
  ;; `res/prove` now discharges a *deferred* antecedent (`lessThan` / `evaluate` /
  ;; `different` / `unknown`) through the registry via `res/*deferred-solver*`, so an
  ;; evaluable conjunct is **computed**, not looked up — and the planned run agrees with
  ;; the unplanned one, since planning only reorders (docs/naf.md).
  (tu/with-terms [age Tom PlanContext]
    (v/assert kb (list age Tom 30) PlanContext)
    (let [goal [(list age '?p '?n) (list 'lessThan '?n 35)]]
      (testing "a true evaluable conjunct is satisfied"
        (is (= 1 (count (v/prove kb goal PlanContext)))))          ; 30 < 35
      (testing "a false one prunes the branch"
        (is (empty? (v/prove kb [(list age '?p '?n) (list 'lessThan '?n 20)] PlanContext))))
      (testing "and the planned run agrees with the unplanned one"
        (is (= (unplanned #(v/prove kb goal PlanContext))
               (v/prove kb goal PlanContext)))))))

;; ---- the read cache: a cost decision, and nothing else -------------------

(deftest the-read-cache-computes-each-distinct-read-once-at-either-arity
  ;; `plan/memoizing` wraps the index reads for the life of one `order` call.  The two
  ;; arities are the two shapes it wraps — `count-at`/`children`/`count-with-functor`
  ;; take an index and one argument, `count-with-arg` takes a position as well — and a
  ;; wrapper that handled only the first would throw on the third.
  (let [calls (volatile! 0)
        f     (fn ([a b]   (vswap! calls inc) [:two a b])
                ([a b c] (vswap! calls inc) [:three a b c]))
        m     (#'plan/memoizing f)]
    (testing "the wrapped answer is returned unchanged, at both arities"
      (is (= [:two :ix [1 2]] (m :ix [1 2])))
      (is (= [:three :ix 1 :Term] (m :ix 1 :Term))))
    (testing "and a repeat is answered from the cache"
      (is (= [:two :ix [1 2]] (m :ix [1 2])))
      (is (= [:three :ix 1 :Term] (m :ix 1 :Term)))
      (is (= 2 @calls) "each distinct read computed exactly once"))
    (testing "a distinct argument at any position is a distinct read"
      (m :ix [1 3])
      (m :ix 2 :Term)
      (m :ix 1 :Other)
      (is (= 5 @calls))))
  (testing "a nil answer is cached as an answer rather than re-asked"
    (let [calls (volatile! 0)
          m     (#'plan/memoizing (fn ([_ _] (vswap! calls inc) nil)
                                    ([_ _ _] (vswap! calls inc) nil)))]
      (is (nil? (m :ix [])))
      (is (nil? (m :ix [])))
      (is (nil? (m :ix 1 :T)))
      (is (nil? (m :ix 1 :T)))
      (is (= 2 @calls)))))

(tu/deftest-kb the-read-cache-changes-no-plan-and-no-estimate
  ;; Caching the index reads is a cost decision, so bypassing it must change nothing:
  ;; the same counts, the same estimates, the same order.  Equality, not closeness —
  ;; `est-matches` bounds a literal from above and `cartesian-factors` reads a bound of
  ;; 1 as a *proof* that the literal matches once, so a number that moved at all would
  ;; be a different plan rather than a slightly worse one.
  (tu/with-terms [linkOne linkTwo tagOf loose Node PlanContext]
    (fan-kb! kb PlanContext linkOne linkTwo Node)
    (v/assert-many kb (concat (for [i (range 6)]
                                (list tagOf (symbol (str Node "C" (mod i 4)))
                                      (symbol (str Node "T" (mod i 2)))))
                              (for [i (range 4)]
                                (list loose (symbol (str Node "L" i))
                                      (symbol (str Node "M" i)))))
                   PlanContext {:chain? false})
    (let [t0    (symbol (str Node "T0"))
          conjs [;; a ground argument in second position, which is what reaches the
                 ;; three-argument read (`count-with-arg`) through `arg-root-estimate`
                 [(list linkOne '?a '?b) (list linkTwo '?b '?c) (list tagOf '?c t0)]
                 [(list tagOf '?c t0) (list linkTwo '?b '?c) (list linkOne '?a '?b)]
                 [(list linkOne '?a '?b) (list loose '?u '?v) (list linkTwo '?b '?c)]
                 [(list tagOf '?c t0) (list loose '?u '?v)]]]
      (doseq [goals conjs]
        (let [planned   (plan/order kb goals PlanContext)
              explained (plan/explain kb goals PlanContext)
              ;; the wrapper replaced by the raw read: same numbers, asked every time
              [raw-plan raw-explain] (with-redefs [plan/memoizing identity]
                                       [(plan/order kb goals PlanContext)
                                        (plan/explain kb goals PlanContext)])]
          (is (= raw-plan planned) (str "order " (pr-str goals)))
          (is (= raw-explain explained) (str "explain " (pr-str goals)))))
      (testing "and the conjunctions were ones the planner actually reordered"
        (is (some (fn [goals] (not= goals (plan/order kb goals PlanContext))) conjs))))))

;; ---- introspection ------------------------------------------------------

(tu/deftest-kb explain-reports-the-plan-with-its-estimates
  (tu/with-terms [parentOf dog Tom Bob Ann PlanContext]
    (v/assert kb (list parentOf Tom Bob) PlanContext)
    (v/assert kb (list dog Bob) PlanContext)
    (v/assert kb (list dog Ann) PlanContext)
    (let [steps (plan/explain kb [(list dog '?y) (list parentOf Tom '?y)] PlanContext)]
      (testing "one step per conjunct, in execution order"
        (is (= 2 (count steps)))
        (is (= parentOf (first (:goal (first steps))))))
      (testing "each step carries the estimate and what was bound when it runs"
        (is (every? #(number? (:est-matches %)) steps))
        (is (= #{} (:bound-before (first steps))))
        (is (contains? (:bound-before (second steps)) '?y))))))

(tu/deftest-kb query-plan-reports-provers-for-a-goal-and-a-join-for-a-conjunction
  (tu/with-terms [parentOf dog Tom Bob Ann PlanContext]
    (v/assert kb (list parentOf Tom Bob) PlanContext)
    (v/assert kb (list dog Bob) PlanContext)
    (v/assert kb (list dog Ann) PlanContext)
    (testing "a single sentence still reports per-prover estimates"
      (let [p (v/query-plan kb (list dog '?y) PlanContext)]
        (is (seq p))
        (is (every? #(contains? % :prover) p))))
    (testing "a vector reports the join plan instead, in execution order"
      (let [p (v/query-plan kb [(list dog '?y) (list parentOf Tom '?y)] PlanContext)]
        (is (= 2 (count p)))
        (is (every? #(contains? % :est-matches) p))
        (is (= parentOf (first (:goal (first p)))))))))
