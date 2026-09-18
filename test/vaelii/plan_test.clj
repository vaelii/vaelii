;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.plan-test
  "Conjunctive query planning (`vaelii.impl.plan`).

  The planner reorders a conjunction for cost, so the two things worth testing are
  that it *does* reorder — the selective literal ends up first however the caller
  wrote it — and that reordering is invisible in the answers.  The second is the one
  that matters: an ordering bug does not throw, it silently returns a different
  answer set, and for a hoisted `evaluate` it silently returns *none*.

  The third is the **cost model itself**, tested before any plan it produces is
  judged.  A plan is two inferences downstream of a bad estimate, so a test that only
  ever asks whether the order came out right reports \"the plan is bad\" without
  reporting that the estimator is why: `q-errors` below measures the estimate against
  the rows a prefix actually returns, per join depth, and flat in the depth is the
  claim that the estimates compose.

  Where a cost claim is made it is made against **rows the engine ran** — every
  permutation costed by asking the engine for each prefix's solutions — rather than
  against the planner's own predicates.  A test that restates the implementation
  inherits its blind spots, and the two that matter here are a conjunct with no
  variables in it and one matching exactly once, neither of which a randomized trial
  over multi-fact relations ever generates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; The planner is pinned ON here whatever the run installed.  `VAELII_PLAN=0` runs the
;; whole suite with conjunctions in the order they were written — the sweep that holds
;; the claim this file's `planning-changes-no-answers-…` makes on twelve trials against
;; every conjunction the suite runs — and under it the questions below have no subject:
;; "the selective literal goes first" is a claim about a planner that is not planning.
;; So this file answers for the shipped planner under every configuration, which keeps
;; its assertion count identical across all of them (`tu/pinning`), and the sweep's work
;; is done by the other 305 namespaces.
(use-fixtures :each (tu/neutral-fresh tu/fresh) (tu/pinning [#'plan/*enabled*]))

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
  (tu/with-terms [parentOf Tom Bob Ann Cid CxPlan]
    (doseq [[p c] [[Tom Bob] [Tom Ann] [Bob Cid] [Ann Cid]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (testing "the trie counts the ground prefix exactly; the open literal is the extent"
      (is (= 2 (plan/est-matches kb (list parentOf Tom '?y) #{})))
      (is (= 4 (plan/est-matches kb (list parentOf '?x '?y) #{}))))
    (testing "a fully ground literal is a test — it matches at most once"
      (is (= 1 (plan/est-matches kb (list parentOf Tom Bob) #{}))))))

(tu/deftest-kb a-bound-token-is-not-charged-an-average
  ;; The one-sidedness `:prune?` rests on, pinned as the case that breaks it.  A bound
  ;; variable takes ONE value at run time, and the value it takes may be the one the
  ;; whole prefix sits under — so charging it `count-at / count-children` is an
  ;; expectation, and an expectation of 1 is not a proof of anything.  Three facts over
  ;; two first arguments average to 1 while the busy argument matches twice.
  (tu/with-terms [parentOf Tom Bob Ann Cid CxPlan]
    (doseq [[p c] [[Tom Bob] [Tom Ann] [Bob Cid]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (let [g (list parentOf '?x '?y)]
      (testing "the estimate is one-sided: it never reads below the true match count"
        (let [est  (plan/est-matches kb g '#{?x})
              true-max (count (v/sentexes-matching kb (list parentOf Tom '?y) CxPlan))]
          (is (= 2 true-max) "Tom is the busy first argument")
          (is (>= est true-max)
              (str "est-matches read " est " for a literal that matches " true-max
                   " times — a :prune? proof off that number is a proof of "
                   "something false"))))
      (testing "so binding a variable does not make the BOUND cheaper — it is not an average"
        (is (= (plan/est-matches kb g #{})
               (plan/est-matches kb g '#{?x}))))
      (testing "the narrowing a binding buys is priced by the join model instead"
        ;; the same literal, joined onto the one-row relation the bound variables are:
        ;; its extent divided by its own distinct count at that position
        (let [step (first (plan/explain kb [g (list 'lessThan 1 2)] CxPlan {:bound '#{?x}}))]
          (is (< (:est-prefix step) (:est-matches step))
              "the prefix estimate narrows where the per-literal bound does not"))))
    (testing "and a literal with everything bound is a test — one-sided and tight"
      (is (= 1 (plan/est-matches kb (list parentOf '?x '?y) '#{?x ?y}))))))

(tu/deftest-kb a-supertype-literal-costs-its-whole-subtree
  (tu/with-terms [animal dog cat Muffet Tom CxPlan]
    (v/assert kb (list 'genl dog animal) CxPlan)
    (v/assert kb (list 'genl cat animal) CxPlan)
    (v/assert kb (list dog Muffet) CxPlan)
    (v/assert kb (list cat Tom) CxPlan)
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
  (tu/with-terms [animal dog Muffet Other CxPlan]
    (v/assert kb (list 'genl dog animal) CxPlan)
    (v/assert kb (list dog Muffet) CxPlan)
    (v/assert kb (list animal Other) CxPlan)
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
  (tu/with-terms [rel dog Tom Bob Rex CxPlan]
    (doseq [[a b] [[Tom Bob] [Bob Tom]]] (v/assert kb (list rel a b) CxPlan))
    (v/assert kb (list dog Rex) CxPlan)
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
        (is (= [sel dotted] (plan/order kb [dotted sel] CxPlan)))
        (is (= [sel dotted] (plan/order kb [sel dotted] CxPlan)))))))

;; ---- the join model: the other estimator --------------------------------
;;
;; `est-matches` bounds one literal from above; `est-rows` says what shape the
;; relation it denotes has, so two of them can be composed.  The two are not
;; interchangeable and the tests below are about the difference.

(defn- chain-with-fan!
  "`a` rows of `linkOne` over `b` distinct second arguments, each of which `linkTwo`
  takes to `c` third ones — so the join is `a·c` rows and neither literal's own extent
  says so."
  [kb ctx linkOne linkTwo Node a b c]
  (v/assert-many kb
                 (concat (for [i (range a)]
                           (list linkOne (symbol (str Node "A" i))
                                 (symbol (str Node "B" (mod i b)))))
                         (for [j (range b), k (range c)]
                           (list linkTwo (symbol (str Node "B" j))
                                 (symbol (str Node "C" j "x" k)))))
                 ctx {:chain? false}))

(tu/deftest-kb est-rows-counts-the-one-column-the-trie-can-reach
  (tu/with-terms [parentOf Tom Bob Ann Cid CxPlan]
    (doseq [[p c] [[Tom Bob] [Tom Ann] [Bob Cid] [Ann Cid]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (testing "the open literal: rows off the prefix, the leading variable off the fan-out"
      ;; three parents (Tom, Bob, Ann) over four facts
      (is (= {:rows 4 :vars '#{?x ?y} :distinct '{?x 3}}
             (plan/est-rows kb (list parentOf '?x '?y)))))
    (testing "a variable the walk cannot reach is absent, not zero"
      ;; ?y sits behind a free position, so the trie stops before it — and the join
      ;; formula reads an absent count as \"ask the other side\", which is why leaving
      ;; it out is a different statement from writing a number in
      (is (not (contains? (:distinct (plan/est-rows kb (list parentOf '?x '?y))) '?y))))
    (testing "a known leading argument moves the countable column along"
      (is (= {:rows 2 :vars '#{?y} :distinct '{?y 2}}
             (plan/est-rows kb (list parentOf Tom '?y)))))
    (testing "a ground literal has no columns at all, and yields one row or none"
      (is (= {:rows 1 :vars #{} :distinct {}} (plan/est-rows kb (list parentOf Tom Bob))))
      (is (= {:rows 0 :vars #{} :distinct {}} (plan/est-rows kb (list parentOf Bob Tom)))))))

(tu/deftest-kb a-variable-repeated-inside-one-literal-is-a-join-and-is-priced-as-one
  ;; `(marriedTo ?x ?x)` is not the extent of `marriedTo`: the second occurrence is an
  ;; equality between two positions, so the literal joins with itself and the same
  ;; formula prices it.  Costed at the whole relation it is the single largest
  ;; over-estimate the trie walk can make, since the true count is a handful of rows —
  ;; and an over-estimated literal is one the planner holds back, so the conjunction it
  ;; should have led runs at full width.
  (tu/with-terms [linksTo Node CxPlan]
    ;; 12 facts over 6 distinct first arguments: 2 rows per leading value
    (doseq [i (range 6), j (range 2)]
      (v/assert kb (list linksTo (symbol (str Node "A" i)) (symbol (str Node "B" i "x" j)))
                CxPlan))
    (let [open (plan/est-rows kb (list linksTo '?x '?y))
          self (plan/est-rows kb (list linksTo '?x '?x))]
      (testing "the open literal is the whole extent, over the column the trie can count"
        (is (= {:rows 12 :vars '#{?x ?y} :distinct '{?x 6}} open)))
      (testing "the repeated variable divides by that column's distinct count"
        ;; 12 rows / 6 distinct leading values = the 2 an average leading value fans to,
        ;; which is what one position matching the other is worth
        (is (= 2 (:rows self)))
        (is (< (:rows self) (:rows open))))
      (testing "and no column carries more distinct values than the narrowed relation has rows"
        (is (every? #(<= % (:rows self)) (vals (:distinct self)))))
      (testing "a third occurrence divides again, and the estimate floors at one row"
        ;; nothing here matches, but the model is an expectation and must not go to zero:
        ;; a zero would rank a literal below a genuinely empty one
        (is (= 1 (:rows (plan/est-rows kb (list linksTo '?x '?x '?x))))))
      (testing "the upper bound is untouched, because it is a bound and this is not one"
        ;; `est-matches` may never be too small, and `(linksTo ?x ?x)` really can match
        ;; every row for all the trie knows
        (is (= 12 (plan/est-matches kb (list linksTo '?x '?x) #{})))))))

(tu/deftest-kb est-rows-reports-rows-and-no-columns-for-the-shapes-the-trie-cannot-walk
  ;; A negative literal keys under [:false …], a dotted rest pins no position, an open
  ;; functor roots nothing — so the walk that counts a column never starts.  Each still
  ;; needs a row count, and it comes from the bound; what must not happen is a column
  ;; being invented, because a fabricated count ranks as a reading in the next join and
  ;; throws away the one the other side actually has.
  (tu/with-terms [rel dog Tom Bob Rex CxPlan]
    (doseq [[a b] [[Tom Bob] [Bob Tom]]] (v/assert kb (list rel a b) CxPlan))
    (v/assert kb (list dog Rex) CxPlan)
    (v/assert kb (list 'not (list rel Rex Rex)) CxPlan)
    (doseq [[what goal] [["a negative literal"  (list 'not (list rel '?x '?y))]
                         ["a dotted rest"       (list rel '. '?args)]
                         ["an open functor"     (list '?p Rex)]]]
      (testing what
        (let [r (plan/est-rows kb goal)]
          (is (pos? (:rows r)) "bounded by something, never floored to zero")
          (is (= {} (:distinct r)) "and no column counted, which reads as ask-the-other-side")
          (is (= (:rows r) (plan/est-matches kb goal #{}))
              "the rows are the bound, these being the shapes with no second model"))))))

(tu/deftest-kb the-two-estimators-answer-different-questions
  ;; `est-matches` may be far too large and may never be too small — a reading of 1 is
  ;; a proof.  `est-rows` is a point estimate and carries no such guarantee.  Nothing
  ;; here should be tempted to fold them into one number.
  (tu/with-terms [animal dog cat Muffet Tom CxPlan]
    (v/assert kb (list 'genl dog animal) CxPlan)
    (v/assert kb (list 'genl cat animal) CxPlan)
    (v/assert kb (list dog Muffet) CxPlan)
    (v/assert kb (list cat Tom) CxPlan)
    (testing "both fan a supertype literal over its subtype closure"
      (is (= 2 (plan/est-matches kb (list animal '?x) #{})))
      (is (= 2 (:rows (plan/est-rows kb (list animal '?x))))))
    (testing "but only est-matches takes the bindings in hand, and it is the bound"
      ;; the closed literal is a test: the bound proves one match, where the row model
      ;; describes the relation and leaves the narrowing to the join
      (is (= 1 (plan/est-matches kb (list animal '?x) '#{?x})))
      (is (= 2 (:rows (plan/est-rows kb (list animal '?x))))))))

(tu/deftest-kb the-counts-span-every-context-and-a-read-is-scoped-to-one
  ;; The trie key ends with the context, so `count-at` under a prefix sums the sentence
  ;; over *every* context it is stored in, while the read the plan is for sees one context
  ;; and the `genlCx` ancestor set above it.  Nothing scopes the counts and nothing can
  ;; cheaply: a per-context count is a second index (docs/inference.md).  Two consequences,
  ;; and they land on the two estimators differently, which is why both are checked here.
  (tu/with-terms [parentOf Tom Bob Cid CxTop CxSub]
    (v/assert kb (list 'genlCx CxSub CxTop) 'CxUniverse
              {:strength :monotonic})
    (doseq [c [CxTop CxSub]]
      (v/assert kb (list parentOf Tom Bob) c {:strength :monotonic}))
    (v/assert kb (list parentOf Tom Cid) CxTop {:strength :monotonic})
    (let [goal (list parentOf Tom '?y)
          seen (fn [c] (count (v/sentexes-matching kb goal c)))]
      (testing "the bound stays sound, which is the property everything rests on"
        ;; a context ancestor set is a subset of what is stored, so a count over all of them can
        ;; only ever be too large — the direction `est-matches` is allowed to be wrong in,
        ;; and the reason a reading of 1 is still a proof
        (is (<= (seen CxTop) (plan/est-matches kb goal #{} {:context CxTop})))
        (is (<= (seen CxSub) (plan/est-matches kb goal #{} {:context CxSub})))
        (is (= (plan/est-matches kb goal #{} {:context CxTop})
               (plan/est-matches kb goal #{} {:context CxSub}))
            "and it is the same number in both, the counts being context-blind"))
      (testing "the inflation lands on the rows and not on the columns"
        ;; the level the walk stops at holds argument values, and the contexts sit a level
        ;; *below* it — so `:distinct` counts what it should while `:rows` counts a
        ;; sentence once per context it is in.  A join divides by the one and multiplies
        ;; by the other, so on a chain this compounds rather than cancelling
        (let [r (plan/est-rows kb goal)]
          (is (= 3 (:rows r)) "(Tom Bob) twice over and (Tom Cid) once")
          (is (= {'?y 2} (:distinct r)) "but Bob and Cid are two values, not three")
          (is (> (:rows r) (seen CxTop)))))
      (testing "a ground literal is clamped, so the multiplicity cannot reach it"
        ;; the one place the walk *does* end on the contexts: a literal with nothing open
        ;; yields one solution or none however many contexts hold it
        (is (= 1 (:rows (plan/est-rows kb (list parentOf Tom Bob)))))
        (is (= 1 (plan/est-matches kb (list parentOf Tom Bob) #{})))))))

(deftest a-join-divides-by-the-side-that-can-count-the-variable
  ;; The formula, on its own, away from any index:
  ;;     rows(A ⋈ B) = rows(A)·rows(B) ÷ Π max(d_A(v), d_B(v))
  ;; with an uncounted column read as 1 — which is what makes a chain work, since the
  ;; trie can count a join variable for the literal it leads and not for the one it
  ;; trails.
  (let [join #'plan/join-summary]
    (testing "the counted side decides"
      (is (= 40.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 20.0}}
                               {:rows 20.0 :vars '#{?b ?c} :distinct '{?b 10.0}})))))
    (testing "with nothing read anywhere there is nothing to divide by, and it is a product"
      (is (= 400.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct {}}
                                {:rows 20.0 :vars '#{?b ?c} :distinct {}})))))
    (testing "but a side that read *some* column lends it as a proxy for one it did not"
      ;; the two-tier rule: a reading beats a guess, and a guess beats nothing.  Where
      ;; neither side read `?b` — it trails a free position on both — dividing by 1
      ;; would call a join a cartesian product, and that is the error that compounds
      ;; fastest with depth, since a chain joined on trailing positions hits it at
      ;; every step
      (is (= 40.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 10.0}}
                               {:rows 20.0 :vars '#{?b ?c} :distinct '{?c 20.0}})))))
    (testing "and the proxy is the smaller of the two, a guess erring towards a larger join"
      ;; an over-large divisor understates a join, which is the direction that puts an
      ;; exploding literal early — so where the model is guessing it guesses low, and
      ;; four rather than ten is the answer that keeps the estimate high
      (is (= 100.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 10.0}}
                                {:rows 20.0 :vars '#{?b ?c} :distinct '{?c 4.0}})))))
    (testing "a reading is never overruled by a proxy, however small the proxy is"
      (is (= 20.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 2.0}}
                               {:rows 20.0 :vars '#{?b ?c} :distinct '{?b 20.0}})))))
    (testing "sharing nothing is a product too"
      (is (= 400.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 20.0}}
                                {:rows 20.0 :vars '#{?c ?d} :distinct '{?c 20.0}})))))
    (testing "the larger count wins the division, since a join cannot exceed either side's"
      (is (= 40.0 (:rows (join {:rows 20.0 :vars '#{?b} :distinct '{?b 2.0}}
                               {:rows 20.0 :vars '#{?b} :distinct '{?b 10.0}})))))
    (testing "the distinct counts propagate, which is what makes a *second* join possible"
      ;; the failure mode this guards: propagate `:rows` and not `:distinct` and the
      ;; next join has nothing to divide by, so the model degenerates to a product
      (let [ab   (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 20.0}}
                       {:rows 20.0 :vars '#{?b ?c} :distinct '{?b 10.0 ?c 5.0}})
            next {:rows 10.0 :vars '#{?c ?d} :distinct '{?c 5.0}}]
        (is (= 40.0 (:rows ab)))
        (is (= '{?a 20.0 ?b 10.0 ?c 5.0} (:distinct ab)))
        (is (= 80.0 (:rows (join ab next))))
        ;; and the failure mode the propagation exists to prevent, which only shows
        ;; where the *other* side cannot read the column either — a third literal whose
        ;; `?c` sits behind a free position, so the trie stops before it.  Drop the
        ;; propagated reading and the same join falls back on a proxy, doubling the
        ;; answer; drop the proxy too and it is a product
        (let [trailing {:rows 10.0 :vars '#{?c ?d} :distinct '{?d 10.0}}
              no-c     (update ab :distinct dissoc '?c)]
          (is (= 80.0  (:rows (join ab trailing))))
          (is (= 40.0  (:rows (join no-c trailing))))
          (is (= 400.0 (:rows (join (assoc no-c :distinct {})
                                    (assoc trailing :distinct {}))))))))
    (testing "no column carries more distinct values than its relation has rows"
      (let [j (join {:rows 3.0 :vars '#{?a ?b} :distinct '{?a 100.0}}
                    {:rows 1.0 :vars '#{?b} :distinct '{?b 50.0}})]
        (is (>= (:rows j) 0.0))
        (is (every? #(<= % (:rows j)) (vals (:distinct j))))))))

(defn- q-errors
  "The model's expected prefix size against the count the engine actually returns for
  that prefix, per join depth: `q = max(est/actual, actual/est)`.

  This is the gate on the cost model itself, and it is measured *before* any claim
  about the plans the model produces — judging a cost model by the cost of its plans
  is two inferences downstream of the defect and reports \"the plan is bad\" without
  reporting that the estimator is why.  Flat in `k` means the estimates compose;
  growing in `k` means they do not, and no amount of better ordering over them would
  rescue that."
  [kb goals ctx]
  (let [steps (plan/explain kb goals ctx)
        order (mapv :goal steps)]
    (mapv (fn [k]
            (let [est (double (max 1 (:est-prefix (nth steps (dec k)))))
                  act (double (max 1 (unplanned #(count (v/prove kb (vec (take k order)) ctx)))))]
              (max (/ est act) (/ act est))))
          (range 1 (inc (count order))))))

(tu/deftest-kb the-join-estimate-is-exact-on-a-uniform-chain-at-every-depth
  ;; Where the model's one assumption holds — arguments independent, fan-out uniform —
  ;; there is nothing to be approximately right about, and being exact at depth 3 is
  ;; the statement that the *composition* is right rather than that depth 1 was.
  (tu/with-terms [linkOne linkTwo linkThree Node CxPlan]
    (chain-with-fan! kb CxPlan linkOne linkTwo Node 24 8 3)
    (v/assert-many kb (for [j (range 8), k (range 3), m (range 2)]
                        (list linkThree (symbol (str Node "C" j "x" k))
                              (symbol (str Node "D" j "x" k "x" m))))
                   CxPlan {:chain? false})
    (let [goals [(list linkOne '?a '?b) (list linkTwo '?b '?c) (list linkThree '?c '?d)]]
      (testing "every prefix of the plan is estimated exactly"
        (is (= [1.0 1.0 1.0] (q-errors kb goals CxPlan))))
      (testing "and the estimates are the numbers a reader would check them against"
        (let [steps (plan/explain kb goals CxPlan)]
          (is (= [24 72 144] (map :est-prefix steps))))))))

(tu/deftest-kb ^:slow the-join-estimate-stays-bounded-when-the-assumption-is-false
  ;; Independence is assumed and is false, so the interesting reading is not whether
  ;; the model is wrong — it is — but whether the error *compounds* with depth.  This
  ;; corpus is deliberately hostile: one hub value takes three quarters of the first
  ;; relation, and the second and third relations' fan-outs vary sharply with the join
  ;; key, so the joint distribution is exactly what per-position counts cannot see.
  (tu/with-terms [linkOne linkTwo linkThree Node CxPlan]
    (v/assert-many kb
                   (concat (for [i (range 40)]
                             (list linkOne (symbol (str Node "A" i))
                                   (symbol (str Node "B" (if (< i 30) 0 (inc (mod i 6)))))))
                           (for [j (range 7), k (range (if (zero? j) 1 (inc (* 2 j))))]
                             (list linkTwo (symbol (str Node "B" j))
                                   (symbol (str Node "C" j "x" k))))
                           (for [j (range 7), k (range (if (zero? j) 1 (inc (* 2 j))))
                                 m (range (if (even? j) 1 4))]
                             (list linkThree (symbol (str Node "C" j "x" k))
                                   (symbol (str Node "D" j "x" k "x" m)))))
                   CxPlan {:chain? false})
    (let [goals [(list linkOne '?a '?b) (list linkTwo '?b '?c) (list linkThree '?c '?d)]
          [q1 q2 q3] (q-errors kb goals CxPlan)]
      (testing "the single-literal estimate is exact — it is a count, not a model"
        (is (= 1.0 q1)))
      (testing "the joins are wrong, and that is the assumption failing as documented"
        (is (< 1.5 q2 6.0) (str "q at depth 2 was " q2)))
      (testing "but the error does not compound: a third join is no worse than the second"
        ;; the whole claim of the model — flat in k, not growing.  A model whose error
        ;; multiplied per join would read q3 ≈ q2² here
        (is (< q3 (* 1.5 q2)) (str "q went " q2 " -> " q3)))
      (testing "and the plan is a function of the conjunction, not of how it was written"
        ;; the same three literals backwards plan to the same order — which is what
        ;; makes the q-error above a reading about the model rather than about the
        ;; order that happened to be measured
        (is (= (mapv :goal (plan/explain kb goals CxPlan))
               (mapv :goal (plan/explain kb (vec (reverse goals)) CxPlan))))))))

(tu/deftest-kb the-bound-variables-are-a-one-row-relation-and-nothing-special
  ;; Sideways information passing has no rule of its own, and this is where it lives:
  ;; the variables already bound are a relation of ONE ROW, and joining a literal onto
  ;; it divides its extent by the literal's own distinct count at that position.  It is
  ;; deliberately NOT `est-matches`' business — that one is a bound, and a bound that
  ;; narrowed on a binding would be an expectation wearing a proof's clothes
  ;; (`a-bound-token-is-not-charged-an-average`).  So the two are pinned apart here:
  ;; the join model narrows, the per-literal bound does not, and neither double-counts.
  (tu/with-terms [parentOf Tom Bob Ann Cid Dee CxPlan]
    (doseq [[p c] [[Tom Bob] [Tom Ann] [Bob Cid] [Ann Cid] [Cid Dee]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (let [g     (list parentOf '?x '?y)
          other (list 'lessThan 1 2)
          step  (first (plan/explain kb [g other] CxPlan {:bound '#{?x}}))
          rows  (:rows (plan/est-rows kb g))
          dx    (get (:distinct (plan/est-rows kb g)) '?x)]
      (testing "the literal's own reading: its extent, and how many values ?x takes over it"
        (is (= 5 rows))
        (is (= 4 dx)))
      (testing "joined onto the one-row relation, the extent is divided by that count"
        (is (= (long (Math/round (/ (double rows) (double dx)))) (:est-prefix step))))
      (testing "while the per-literal bound stays the whole extent, bound or not"
        (is (= rows (plan/est-matches kb g '#{?x}) (plan/est-matches kb g #{})))))))

;; ---- ordering -----------------------------------------------------------

(tu/deftest-kb an-open-functor-leads-when-it-is-the-selective-literal
  (tu/with-terms [animal dog cat bird Muffet CxPlan]
    ;; a type hierarchy wide enough that walking it is dearer than reading Muffet's
    ;; own memberships, which is the whole point of leading with the latter
    (doseq [t [dog cat bird]] (v/assert kb (list 'genl t animal) CxPlan))
    (v/assert kb (list dog Muffet) CxPlan)
    (let [open   (list '?c Muffet)
          hier   (list 'genl '?c animal)
          answers (fn [gs] (set (map #(get % '?c) (v/prove kb gs CxPlan))))]
      (testing "written either way, the open functor is picked first"
        (is (= [open hier] (plan/order kb [open hier] CxPlan)))
        (is (= [open hier] (plan/order kb [hier open] CxPlan))))
      (testing "and the reordering changes no answers"
        (let [expected (unplanned #(answers [open hier]))]
          (is (seq expected))
          (is (= expected (answers [open hier])))
          (is (= expected (answers [hier open])))
          (is (= expected (unplanned #(answers [hier open])))))))))

(tu/deftest-kb the-selective-literal-goes-first-however-it-was-written
  (tu/with-terms [parentOf dog Tom Bob Ann Cid CxPlan]
    (doseq [[p c] [[Tom Bob] [Bob Cid] [Ann Cid]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (doseq [d [Bob Cid Ann]] (v/assert kb (list dog d) CxPlan))
    (let [selective (list parentOf Tom '?y)
          general   (list dog '?y)]
      (testing "written selective-first, it stays first"
        (is (= [selective general] (plan/order kb [selective general] CxPlan))))
      (testing "written general-first, the planner swaps it"
        (is (= [selective general] (plan/order kb [general selective] CxPlan)))))))

(tu/deftest-kb planning-is-deterministic-and-breaks-ties-on-written-order
  (tu/with-terms [likes Tom Bob CxPlan]
    (v/assert kb (list likes Tom Bob) CxPlan)
    (let [a (list likes '?x '?y)
          b (list likes '?y '?z)
          conj- [a b]]
      (testing "the same conjunction plans the same way every time"
        (is (apply = (repeatedly 5 #(plan/order kb conj- CxPlan)))))
      (testing "equal-cost literals keep the order they were written in"
        (is (= a (first (plan/order kb [a b] CxPlan))))))))

(tu/deftest-kb a-repeated-conjunct-is-not-dropped
  (tu/with-terms [parentOf Tom Bob CxPlan]
    (v/assert kb (list parentOf Tom Bob) CxPlan)
    (testing "planning is a permutation — it never shortens the conjunction"
      (let [g (list parentOf '?x '?y)]
        (is (= 3 (count (plan/order kb [g g g] CxPlan))))))))

;; ---- costing the plan, not the next literal -----------------------------

(defn- chain-kb!
  "A 1:1 chain `link1 ?a ?b`, `link2 ?b ?c`, `link3 ?c ?d` of `n` facts each, plus a
  `loose` relation of `few` facts sharing no variable with them.

  This is the form a per-literal cost model gets wrong.  `loose` is the smallest
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
  (tu/with-terms [linkOne linkTwo linkThree loose Node CxPlan]
    (chain-kb! kb CxPlan [linkOne linkTwo linkThree loose Node] 6 3)
    (let [c1      (list linkOne '?a '?b)
          c2      (list linkTwo '?b '?c)
          c3      (list linkThree '?c '?d)
          lo      (list loose '?u '?v)
          written [lo c1 c2 c3]]
      (testing "`loose` really is the cheapest literal taken on its own"
        (is (< (plan/est-matches kb lo #{}) (plan/est-matches kb c1 #{}))))
      (testing "and it is still planned last, because its bindings buy nothing"
        (is (= [c1 c2 c3 lo] (plan/order kb written CxPlan))))
      (testing "which is the order with the fewest intermediate rows"
        (is (= (actual-rows kb [c1 c2 c3 lo] CxPlan)
               (apply min (map #(actual-rows kb % CxPlan)
                               (permutations written))))))
      (testing "and the plan reports *why* it is last, not just a small estimate there"
        (let [rows (plan/explain kb written CxPlan)]
          (is (= [lo] (map :goal (filter :isolated? rows))))
          ;; the trap the flag exists for: it is the cheapest literal in the
          ;; conjunction and sits last, which without a reason is indistinguishable from a mistake
          (is (:isolated? (last rows)))
          (is (< (:est-matches (last rows)) (:est-matches (first rows)))))))))

(tu/deftest-kb at-two-literals-the-cheaper-one-leads-and-that-is-already-optimal
  ;; Two is the common width — a rule's antecedents — and the width at which costing
  ;; the plan and costing the next literal provably agree: both orders end on the same
  ;; join, so the costs differ only by the leading literal's own extent.  Pinned
  ;; because it is why the search is not run here, not merely why it need not be.
  (tu/with-terms [linkOne linkTwo linkThree loose Node CxPlan]
    (chain-kb! kb CxPlan [linkOne linkTwo linkThree loose Node] 6 3)
    (let [c1 (list linkOne '?a '?b)
          lo (list loose '?u '?v)]
      (testing "the cheaper literal leads, written either way"
        (is (< (plan/est-matches kb lo #{}) (plan/est-matches kb c1 #{})))
        (is (= [lo c1] (plan/order kb [lo c1] CxPlan)))
        (is (= [lo c1] (plan/order kb [c1 lo] CxPlan))))
      (testing "and no permutation of the pair runs fewer rows"
        (is (= (actual-rows kb [lo c1] CxPlan)
               (min (actual-rows kb [lo c1] CxPlan)
                    (actual-rows kb [c1 lo] CxPlan))))))))

(tu/deftest-kb the-planned-order-is-the-cheapest-of-every-permutation
  (tu/with-terms [linkOne linkTwo linkThree loose Node CxPlan]
    (chain-kb! kb CxPlan [linkOne linkTwo linkThree loose Node] 5 2)
    (let [conjuncts [(list loose '?u '?v)
                     (list linkOne '?a '?b)
                     (list linkTwo '?b '?c)
                     (list linkThree '?c '?d)]]
      (testing "the search is exact, not merely better: no permutation runs fewer rows"
        (let [planned (plan/order kb conjuncts CxPlan)
              costs   (map #(actual-rows kb % CxPlan) (permutations conjuncts))]
          (is (= (actual-rows kb planned CxPlan) (apply min costs)))))
      (testing "and the cartesian factor is last however the conjunction was written"
        ;; the connected head may still differ between permutations — those literals
        ;; have equal extents, and a cost tie resolves to written order by design
        (doseq [p (permutations conjuncts)]
          (is (= (list loose '?u '?v) (last (plan/order kb p CxPlan)))))))))

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

(tu/deftest-kb ^:slow planning-changes-no-answers-over-randomized-conjunctions
  ;; The invariant, over shapes nobody chose: whatever the planner did to a
  ;; conjunction, the answers are the answers.  This corpus is deliberately tiny —
  ;; relations of a few facts each, which is what makes an exhaustive check cheap —
  ;; and correspondingly says nothing about *cost*: a plan that runs nine rows where
  ;; the best runs two is a fact about small integers.  The cost claim is made on a
  ;; corpus sized for it, below.
  (tu/with-terms [rel Node CxPlan]
    (let [rng    (java.util.Random. 20260730)
          trials (for [trial (range 12)]
                   (let [conjuncts (random-trial! kb CxPlan rel Node rng trial)]
                     {:conjuncts conjuncts
                      :planned   (plan/order kb conjuncts CxPlan)
                      :isolated  (isolated-literals conjuncts)}))]
      (testing "the trials threw up cartesian factors to place at all"
        (is (seq (filter #(seq (:isolated %)) trials))))
      (testing "and the planner reordered something, or this proves nothing"
        (is (some #(not= (:conjuncts %) (:planned %)) trials)))
      (testing "every planned order returns exactly the unplanned answer set"
        (doseq [{:keys [conjuncts planned]} trials]
          (let [answers (fn [gs] (set (v/prove kb gs CxPlan)))]
            (is (= (unplanned #(answers conjuncts)) (answers planned)))))))))

(defn- oracle-trial!
  "One randomized four-way join big enough for a row count to mean something:
  relations of 15–60 facts over a shared pool of individuals, and four literals whose
  variables are drawn from a pool small enough that some share and some do not.

  Deliberately larger than `random-trial!`'s corpus, and the reason is the
  measurement rather than the coverage.  A relation of three facts joins to a handful
  of rows, where the difference between a good plan and a bad one is a couple of rows
  and the *ratio* between them is granularity — a trial whose best order runs 2 rows
  and whose planned order runs 21 reports 10×, which is a fact about small integers.
  At this size a ratio is about the plan."
  [kb ctx rel-base node-base ^java.util.Random rng trial]
  (let [rel  (fn [i] (symbol (str rel-base "t" trial "x" i)))
        node (fn [i] (symbol (str node-base "N" i)))
        pool 14
        vars '[?p ?q ?r ?s ?t]]
    (v/assert-many kb
                   (distinct (for [i (range 4)
                                   _ (range (+ 15 (.nextInt rng 45)))]
                               (list (rel i) (node (.nextInt rng pool))
                                     (node (.nextInt rng pool)))))
                   ctx {:chain? false})
    (mapv (fn [i] (list (rel i)
                        (nth vars (.nextInt rng (count vars)))
                        (nth vars (.nextInt rng (count vars)))))
          (range 4))))

(tu/deftest-kb ^:slow the-planned-order-runs-close-to-the-best-permutation
  ;; The honest measure of a cost model is not whether the plans changed but whether
  ;; they run fewer rows, and the only way to know that without another model to argue
  ;; with is an oracle: all twenty-four permutations, costed by the engine.
  ;;
  ;; The claim is made on the **totals** and not on a mean of per-trial ratios.  A mean
  ;; of ratios is dominated by whichever trial had the smallest oracle, which is the
  ;; trial whose ratio carries the least information; totals weight a trial by how many
  ;; rows it actually ran, which is what a cost model is for.
  (tu/with-terms [rel Node CxPlan]
    (let [rng     (java.util.Random. 20260809)
          trials  (vec (for [trial (range 12)]
                         (let [conjuncts (oracle-trial! kb CxPlan rel Node rng trial)
                               costs     (map #(actual-rows kb % CxPlan)
                                              (permutations conjuncts))
                               planned   (plan/order kb conjuncts CxPlan)]
                           {:planned (actual-rows kb planned CxPlan)
                            :best    (apply min costs)
                            :worst   (apply max costs)})))
          total   (fn [k] (reduce + (map k trials)))]
      (testing "the trials are joins with room to get wrong — the orders differ widely"
        (is (< (* 4 (total :best)) (total :worst))))
      (testing "no plan beats the oracle, which would mean the oracle was measured wrong"
        (is (every? #(<= (:best %) (:planned %)) trials)))
      (testing "the planned orders run within a quarter of the best possible, in total"
        (is (< (total :planned) (* 1.25 (total :best)))
            (str "planned " (total :planned) " against best " (total :best))))
      (testing "and every single plan is nearer its best permutation than its worst"
        ;; a per-trial claim that survives the small trials: where the best order runs
        ;; two rows and the plan runs nine, a *ratio* reads 4.5x and means very little,
        ;; but landing in the lower half of the spread still means something
        (is (every? #(<= (* 2 (:planned %)) (+ (:best %) (:worst %))) trials)
            (pr-str (remove #(<= (* 2 (:planned %)) (+ (:best %) (:worst %))) trials)))))))

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
  (tu/with-terms [linkOne linkTwo guard Node CxPlan]
    (fan-kb! kb CxPlan linkOne linkTwo Node)
    (let [g       (list guard (symbol (str Node "Zed")))   ; asserted nowhere: no match
          c1      (list linkOne '?a '?b)
          c2      (list linkTwo '?b '?c)
          written [c1 c2 g]]
      (testing "it is the cheapest literal present, and soundly so — a test matches once"
        (is (= 1 (plan/est-matches kb g #{}))))
      (testing "so it leads, and the join behind it is never run"
        (is (= [g c1 c2] (plan/order kb written CxPlan)))
        (is (zero? (actual-rows kb [g c1 c2] CxPlan)))
        (is (pos? (actual-rows kb [c1 c2 g] CxPlan))))
      (testing "which is the order with the fewest intermediate rows"
        (is (= (actual-rows kb [g c1 c2] CxPlan)
               (apply min (map #(actual-rows kb % CxPlan)
                               (permutations written))))))
      (testing "and the plan does not claim it was held back as a cartesian factor"
        (is (not-any? :isolated? (plan/explain kb written CxPlan))))
      (testing "it is a block of its own, having no variable to share with anything"
        ;; the edge every placement rule owes a case: a conjunct with no variables in
        ;; it satisfies any \"shares nothing\" test vacuously, and the block split has
        ;; to put it somewhere
        (let [steps (plan/explain kb written CxPlan)]
          (is (= [0 1 1] (map :block steps)))
          (is (= 0 (:est-rows (first steps)))))))))

(tu/deftest-kb an-est-override-replaces-the-index-model-and-counts-no-columns
  ;; The extension point a caller whose executor's leaf is the prover registry opts into: a `genl`
  ;; conjunct is answered from the cached closure, so what it costs is the closure's
  ;; size and not the handful of stored edges the trie can count.  An override reports
  ;; a row count and nothing at all about columns, so every join with it defers to
  ;; whatever the other side can read — which preserves the fan-out the override exists
  ;; to report, where an invented column count would divide it away again.
  (tu/with-terms [wide narrow Node CxPlan]
    (v/assert-many kb (concat (for [i (range 3)]
                                (list wide (symbol (str Node "W" i)) (symbol (str Node "S" i))))
                              (for [i (range 12)]
                                (list narrow (symbol (str Node "S" (mod i 4)))
                                      (symbol (str Node "T" i)))))
                   CxPlan {:chain? false})
    (let [w (list wide '?w '?s)
          n (list narrow '?s '?t)
          huge (fn [g _] (when (= g w) 5000))]
      (testing "by the index the wide literal is the cheaper, and it leads"
        (is (< (plan/est-matches kb w #{}) (plan/est-matches kb n #{})))
        (is (= [w n] (plan/order kb [n w] CxPlan))))
      (testing "told it costs five thousand, the planner leads with the other one"
        (is (= [n w] (plan/order kb [n w] CxPlan {:est-override huge})))
        (is (= [n w] (plan/order kb [w n] CxPlan {:est-override huge}))))
      (testing "and `explain` reports the model that chose the order, not the one it replaced"
        ;; the failure this pins: an order chosen under the override, reported with the
        ;; index's own numbers beside it — a plan whose stated reason contradicts it,
        ;; which is worse than no reason, since the number is what a reader debugs from
        (let [[a b :as steps] (plan/explain kb [w n] CxPlan {:est-override huge})]
          (is (= [n w] (mapv :goal steps)))
          (is (= 5000 (:est-matches b)) "the overridden literal reports what it was costed at")
          (is (= 5000 (:est-rows b)))
          (is (= (plan/est-matches kb n #{}) (:est-matches a))
              "and one the override declines to answer falls back on the index model")
          (is (= (:rows (plan/est-rows kb n)) (:est-rows a))))
        ;; an override answering for every literal must not leave a column behind either:
        ;; it reports rows and nothing about columns, so the prefix is their product
        (let [flat  (fn [_ _] 7)
              steps (plan/explain kb [w n] CxPlan {:est-override flat})]
          (is (every? #(= 7 (:est-matches %)) steps))
          (is (= [7 49] (mapv :est-prefix steps))))))))

(tu/deftest-kb an-unshared-literal-that-cannot-fan-out-leads-too
  ;; The same rule stated over an estimate rather than over structure.  `loose` shares
  ;; no variable, but one fact matches it, so it multiplies by one: it cannot fan the
  ;; plan out, only sit in it.  `est-matches` bounds from above, so an estimate of 1
  ;; *proves* that — the one direction the bound is sound in.
  (tu/with-terms [linkOne linkTwo loose Node CxPlan]
    (fan-kb! kb CxPlan linkOne linkTwo Node)
    (v/assert kb (list loose (symbol (str Node "U0")) (symbol (str Node "V0"))) CxPlan)
    (let [lo      (list loose '?u '?v)
          c1      (list linkOne '?a '?b)
          c2      (list linkTwo '?b '?c)
          written [c1 c2 lo]]
      (is (= 1 (plan/est-matches kb lo #{})))
      (testing "it leads, and running it last would cost strictly more"
        (is (= [lo c1 c2] (plan/order kb written CxPlan)))
        (is (< (actual-rows kb [lo c1 c2] CxPlan)
               (actual-rows kb [c1 c2 lo] CxPlan))))
      (testing "a second fact stops it being *proved* harmless, so the law ranks it"
        ;; Not the same claim, and the difference is the point.  The bound no longer
        ;; waves it through as a test, so it is a block to place — and against a chain
        ;; that fans out behind it the transposition law still leads with it, which is
        ;; the cheaper order by the rows the engine runs.  Nothing was held back, so
        ;; nothing is flagged as having been.
        (v/assert kb (list loose (symbol (str Node "U1")) (symbol (str Node "V1")))
                  CxPlan)
        (is (= 2 (plan/est-matches kb lo #{})))
        (is (= [lo c1 c2] (plan/order kb written CxPlan)))
        (is (< (actual-rows kb [lo c1 c2] CxPlan)
               (actual-rows kb [c1 c2 lo] CxPlan)))
        (is (not-any? :isolated? (plan/explain kb written CxPlan)))))))

(tu/deftest-kb a-cartesian-factor-changes-places-where-the-transposition-law-says-it-does
  ;; \"A cartesian factor runs last\" is a *consequence* of the ordering law and not a
  ;; rule of its own, and it therefore has a crossover — which is the sharpest test of
  ;; the law there is, because the implementation has to change its answer at the point
  ;; the arithmetic does and the engine's own row counts say where that is.
  ;;
  ;; A block of `n` rows costing `s` intermediates belongs before another when
  ;; `s/(n−1)` is the larger.  The chain here is 20 rows fanning to 80, so `s/(n−1)` =
  ;; 100/79 ≈ 1.27; a disconnected relation of `m` rows reads `m/(m−1)`, which is above
  ;; that at four rows and below it at five.  Both sides are checked against the rows
  ;; the engine actually runs, so this is the law being right rather than the
  ;; implementation agreeing with itself.
  (tu/with-terms [linkOne linkTwo four five Node CxPlan]
    (fan-kb! kb CxPlan linkOne linkTwo Node)
    (v/assert-many kb (concat (for [i (range 4)]
                                (list four (symbol (str Node "U" i)) (symbol (str Node "V" i))))
                              (for [i (range 5)]
                                (list five (symbol (str Node "W" i)) (symbol (str Node "X" i)))))
                   CxPlan {:chain? false})
    (let [c1 (list linkOne '?a '?b)
          c2 (list linkTwo '?b '?c)
          lo4 (list four '?u '?v)
          lo5 (list five '?u '?v)]
      (testing "four rows is inexpensive enough to lead the chain; five is not"
        (is (= [lo4 c1 c2] (plan/order kb [c1 c2 lo4] CxPlan)))
        (is (= [c1 c2 lo5] (plan/order kb [c1 c2 lo5] CxPlan))))
      (testing "and each is the cheapest permutation, by the rows the engine runs"
        (doseq [written [[c1 c2 lo4] [c1 c2 lo5]]]
          (is (= (actual-rows kb (plan/order kb written CxPlan) CxPlan)
                 (apply min (map #(actual-rows kb % CxPlan) (permutations written))))
              (pr-str written))))
      (testing "only the one that was held back is reported as held back"
        (is (not-any? :isolated? (plan/explain kb [c1 c2 lo4] CxPlan)))
        (is (= [lo5] (map :goal (filter :isolated? (plan/explain kb [c1 c2 lo5] CxPlan)))))))))

(tu/deftest-kb two-literals-disconnected-from-the-rest-but-not-from-each-other-are-one-block
  ;; The placement rule read one literal at a time, and that was its reach: a *pair*
  ;; sharing a variable with each other and with nothing else multiplies the plan just
  ;; as much, and neither of them is isolated, because each shares a variable with
  ;; something.  Components are what see it.  Here the small pair belongs in front of
  ;; the large one and the old reading had no way to say so — it would have run all
  ;; four in one cheapest-first pool and led with whichever literal happened to be
  ;; smallest.
  (tu/with-terms [bigOne bigTwo smallOne smallTwo Node CxPlan]
    (v/assert-many kb
                   (concat (for [i (range 30)]
                             (list bigOne (symbol (str Node "A" i))
                                   (symbol (str Node "B" (mod i 6)))))
                           (for [j (range 6), k (range 3)]
                             (list bigTwo (symbol (str Node "B" j))
                                   (symbol (str Node "C" j "x" k))))
                           (for [i (range 4)]
                             (list smallOne (symbol (str Node "P" i)) (symbol (str Node "Q" i))))
                           (for [i (range 4)]
                             (list smallTwo (symbol (str Node "Q" i)) (symbol (str Node "R" i)))))
                   CxPlan {:chain? false})
    (let [s1 (list smallOne '?p '?q)
          s2 (list smallTwo '?q '?r)
          b1 (list bigOne '?a '?b)
          b2 (list bigTwo '?b '?c)
          written [s1 b1 s2 b2]
          planned (plan/order kb written CxPlan)
          steps   (plan/explain kb written CxPlan)
          block   (into {} (map (juxt :goal :block)) steps)]
      (testing "the two pairs are two blocks, and each ran contiguously"
        (is (= (block s1) (block s2)))
        (is (= (block b1) (block b2)))
        (is (not= (block s1) (block b1)))
        (is (= [0 0 1 1] (map block planned))))
      (testing "neither literal is a cartesian factor, and neither was flagged as one"
        ;; each shares a variable with its partner, so the one-literal-at-a-time test
        ;; says nothing about either — which is what made this shape invisible
        (is (not-any? :isolated? steps)))
      (testing "the small block leads, and that is the cheapest order of the twenty-four"
        (is (= [s1 s2] (take 2 planned)))
        (is (= (actual-rows kb planned CxPlan)
               (apply min (map #(actual-rows kb % CxPlan) (permutations written))))))
      (testing "and interleaving the two blocks costs more, which is why they moved together"
        (is (< (actual-rows kb planned CxPlan)
               (actual-rows kb [s1 b1 s2 b2] CxPlan)))))))

(tu/deftest-kb a-block-the-caller-already-narrowed-runs-before-one-it-did-not
  ;; The anchored block: every component reached by the caller's bindings, a deferred
  ;; literal or the recursive literal is fused into one and placed first.  Both are
  ;; selectivity the summary algebra does not model — an evaluable prunes on values,
  ;; and a bound variable narrows a literal in a way a rival block's own `n` cannot
  ;; account for — so the law would be ranking those blocks on numbers that leave the
  ;; narrowing out.
  (tu/with-terms [known other Node CxPlan]
    (v/assert-many kb (concat (for [i (range 12)]
                                (list known (symbol (str Node "K" (mod i 4)))
                                      (symbol (str Node "L" i))))
                              (for [i (range 3)]
                                (list other (symbol (str Node "M" i)) (symbol (str Node "N" i)))))
                   CxPlan {:chain? false})
    (let [anchored (list known '?k '?l)
          loose    (list other '?m '?n)
          steps    (plan/explain kb [loose anchored] CxPlan {:bound '#{?k}})]
      (testing "the narrowed literal leads, though its own extent is the larger"
        (is (< (plan/est-matches kb loose #{}) (plan/est-matches kb anchored #{})))
        (is (= [anchored loose] (plan/order kb [loose anchored] CxPlan {:bound '#{?k}}))))
      (testing "and the plan says which block did it"
        (is (= [0 1] (map :block steps)))))))

(tu/deftest-kb a-literal-feeding-an-evaluable-is-not-a-cartesian-factor
  ;; `age` shares no variable with either chain literal, so read against the
  ;; generators alone it looks isolated and would be held to the back — taking the
  ;; evaluable that consumes its binding with it, and costing the run the early prune
  ;; that evaluable exists to give.  Sharing is therefore judged against every literal
  ;; the caller wrote, the deferred ones included.  Nothing else in this namespace
  ;; fails if that widening is dropped.
  (tu/with-terms [linkOne linkTwo age Person Node CxPlan]
    (doseq [i (range 6)]
      (v/assert kb (list linkOne (symbol (str Node "A" i)) (symbol (str Node "B" i))) CxPlan)
      (v/assert kb (list linkTwo (symbol (str Node "B" i)) (symbol (str Node "C" i))) CxPlan))
    (v/assert kb (list age (symbol (str Person "One")) 30) CxPlan)
    (v/assert kb (list age (symbol (str Person "Two")) 40) CxPlan)
    (let [ordered (plan/order kb [(list linkOne '?a '?b)
                                  (list linkTwo '?b '?c)
                                  (list age '?p '?n)
                                  (list 'lessThan '?n 35)]
                              CxPlan)]
      (testing "it leads on its own cost, rather than being deferred as isolated"
        (is (= (list age '?p '?n) (first ordered))))
      (testing "so the evaluable it binds is pulled forward behind it, and prunes early"
        (is (= 'lessThan (first (second ordered)))))
      (testing "and the plan says so: nothing here is reported as a cartesian factor"
        (is (not-any? :isolated? (plan/explain kb [(list linkOne '?a '?b)
                                                   (list linkTwo '?b '?c)
                                                   (list age '?p '?n)
                                                   (list 'lessThan '?n 35)]
                                               CxPlan)))))))

;; ---- what must never be reordered ---------------------------------------

(tu/deftest-kb a-deferred-literal-never-outruns-what-binds-it
  (tu/with-terms [age Tom Bob CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (v/assert kb (list age Bob 40) CxPlan)
    (testing "an evaluable stays behind the literal binding its arguments"
      (let [ordered (plan/order kb [(list 'lessThan '?n 35) (list age '?p '?n)] CxPlan)]
        (is (= age (first (first ordered))))
        (is (= 'lessThan (first (second ordered))))))
    (testing "so does an evaluate — hoisting one yields no solutions rather than an error"
      (let [ordered (plan/order kb [(list 'evaluate '?z (list '+ '?n 1)) (list age '?p '?n)]
                                CxPlan)]
        (is (= age (first (first ordered))))))))

(tu/deftest-kb a-deferred-literal-is-pulled-forward-once-its-variables-are-bound
  (tu/with-terms [age likes Tom Bob CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (v/assert kb (list likes Tom Bob) CxPlan)
    (testing "a test that can run early prunes early — it does not sit uniformly last"
      (let [ordered (plan/order kb [(list age '?p '?n)
                                    (list 'lessThan '?n 35)
                                    (list likes '?p '?q)]
                                CxPlan)]
        ;; the filter on ?n belongs directly after the literal that binds ?n, not
        ;; after the unrelated `likes` join it would otherwise multiply through
        (is (= 'lessThan (first (nth ordered 1))))))))

(tu/deftest-kb the-recursive-literal-stays-last-so-recursion-still-terminates
  (tu/with-terms [parentOf ancestorOf Aa Bb Cc Dd CxPlan]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) CxPlan {:direction :forward})
    (v/assert-rule kb [(list parentOf '?x '?y) (list ancestorOf '?y '?z)]
                   (list ancestorOf '?x '?z) CxPlan {:direction :forward})
    (doseq [[p c] [[Aa Bb] [Bb Cc] [Cc Dd]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (testing "the literal sharing the consequent's functor is pinned last"
      (let [ordered (plan/order kb [(list ancestorOf '?y '?z) (list parentOf '?x '?y)]
                                CxPlan {:consequent-pred ancestorOf})]
        (is (= parentOf   (first (first ordered))))
        (is (= ancestorOf (first (second ordered))))))
    (testing "so a right-recursive rule still terminates and closes transitively"
      (is (= #{Bb Cc Dd}
             (set (map #(get % '?who)
                       (v/prove kb (list ancestorOf Aa '?who) CxPlan))))))))

;; ---- the invariant: cost changes, meaning does not -----------------------

(tu/deftest-kb planning-never-changes-the-answer-set
  (tu/with-terms [parentOf dog cat Tom Bob Ann Cid CxPlan]
    (doseq [[p c] [[Tom Bob] [Tom Ann] [Bob Cid] [Ann Cid]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (v/assert kb (list dog Bob) CxPlan)
    (v/assert kb (list dog Cid) CxPlan)
    (v/assert kb (list cat Ann) CxPlan)
    (let [conjuncts [(list parentOf Tom '?y) (list dog '?y) (list parentOf '?y '?z)]
          answers   (fn [gs] (set (map #(select-keys % '[?y ?z]) (v/prove kb gs CxPlan))))
          expected  (unplanned #(answers conjuncts))]
      (testing "the query has answers at all — otherwise this proves nothing"
        (is (seq expected)))
      (testing "every permutation, planned, gives exactly the unplanned answer set"
        (doseq [p (permutations conjuncts)]
          (is (= expected (answers p)) (str "permutation " (pr-str p)))
          (is (= expected (unplanned #(answers p))) (str "unplanned " (pr-str p))))))))

(tu/deftest-kb planning-never-changes-the-answer-set-through-a-rule
  (tu/with-terms [parentOf grandparentOf dog Tom Bob Ann Cid CxPlan]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) CxPlan {:direction :forward})
    (doseq [[p c] [[Tom Bob] [Bob Cid] [Tom Ann] [Ann Cid]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (v/assert kb (list dog Cid) CxPlan)
    (let [goal    [(list grandparentOf Tom '?z) (list dog '?z)]
          answers (fn [gs] (set (map #(get % '?z) (v/prove kb gs CxPlan))))]
      (testing "a planned rule expansion agrees with an unplanned one"
        (is (= #{Cid} (answers goal)))
        (is (= (unplanned #(answers goal)) (answers goal))))
      (testing "and so does the reversed conjunction"
        (is (= (answers goal) (answers (vec (reverse goal)))))))))

(tu/deftest-kb an-evaluable-antecedent-still-computes-under-planning
  ;; An evaluable is reachable through the *prover* stack, so the conjunction that
  ;; exercises it is a rule's antecedents (planned by `provers/planned-antecedents`)
  ;; rather than a `prove` goal vector — see the limitation pinned below.
  (tu/with-terms [age young Tom Bob Cid CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (v/assert kb (list age Bob 40) CxPlan)
    (v/assert kb (list age Cid 20) CxPlan)
    (v/assert-rule kb [(list age '?p '?n) (list 'lessThan '?n 35)]
                   (list young '?p) CxPlan {:direction :forward})
    (let [answers (fn [] (set (map #(get % '?p) (v/ask kb (list young '?p) CxPlan))))]
      (testing "the filter applies — a hoisted evaluable would silently answer none"
        (is (= #{Tom Cid} (answers))))
      (testing "and the planned run agrees with the unplanned one"
        (is (= (unplanned answers) (answers)))))))

(tu/deftest-kb prove-evaluates-an-evaluable-conjunct
  ;; `res/prove` now discharges a *deferred* antecedent (`lessThan` / `evaluate` /
  ;; `different` / `unknown`) through the registry via `res/*deferred-solver*`, so an
  ;; evaluable conjunct is **computed**, not looked up — and the planned run agrees with
  ;; the unplanned one, since planning only reorders (docs/naf.md).
  (tu/with-terms [age Tom CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (let [goal [(list age '?p '?n) (list 'lessThan '?n 35)]]
      (testing "a true evaluable conjunct is satisfied"
        (is (= 1 (count (v/prove kb goal CxPlan)))))          ; 30 < 35
      (testing "a false one prunes the branch"
        (is (empty? (v/prove kb [(list age '?p '?n) (list 'lessThan '?n 20)] CxPlan))))
      (testing "and the planned run agrees with the unplanned one"
        (is (= (unplanned #(v/prove kb goal CxPlan))
               (v/prove kb goal CxPlan)))))))

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
  ;; `est-matches` bounds a literal from above and `rank-blocks` reads a whole block of
  ;; such bounds coming back 1 as a *proof* that the block cannot multiply, so a number
  ;; that moved at all would be a different plan rather than a slightly worse one.
  (tu/with-terms [linkOne linkTwo tagOf loose Node CxPlan]
    (fan-kb! kb CxPlan linkOne linkTwo Node)
    (v/assert-many kb (concat (for [i (range 6)]
                                (list tagOf (symbol (str Node "C" (mod i 4)))
                                      (symbol (str Node "T" (mod i 2)))))
                              (for [i (range 4)]
                                (list loose (symbol (str Node "L" i))
                                      (symbol (str Node "M" i)))))
                   CxPlan {:chain? false})
    (let [t0    (symbol (str Node "T0"))
          conjs [;; a ground argument in second position, which is what reaches the
                 ;; three-argument read (`count-with-arg`) through `arg-root-estimate`
                 [(list linkOne '?a '?b) (list linkTwo '?b '?c) (list tagOf '?c t0)]
                 [(list tagOf '?c t0) (list linkTwo '?b '?c) (list linkOne '?a '?b)]
                 [(list linkOne '?a '?b) (list loose '?u '?v) (list linkTwo '?b '?c)]
                 [(list tagOf '?c t0) (list loose '?u '?v)]]]
      (doseq [goals conjs]
        (let [planned   (plan/order kb goals CxPlan)
              explained (plan/explain kb goals CxPlan)
              ;; the wrapper replaced by the raw read: same numbers, asked every time
              [raw-plan raw-explain] (with-redefs [plan/memoizing identity]
                                       [(plan/order kb goals CxPlan)
                                        (plan/explain kb goals CxPlan)])]
          (is (= raw-plan planned) (str "order " (pr-str goals)))
          (is (= raw-explain explained) (str "explain " (pr-str goals)))))
      (testing "and the conjunctions were ones the planner actually reordered"
        (is (some (fn [goals] (not= goals (plan/order kb goals CxPlan))) conjs))))))

;; ---- introspection ------------------------------------------------------

(tu/deftest-kb explain-reports-the-plan-with-its-estimates
  (tu/with-terms [parentOf dog Tom Bob Ann CxPlan]
    (v/assert kb (list parentOf Tom Bob) CxPlan)
    (v/assert kb (list dog Bob) CxPlan)
    (v/assert kb (list dog Ann) CxPlan)
    (let [steps (plan/explain kb [(list dog '?y) (list parentOf Tom '?y)] CxPlan)]
      (testing "one step per conjunct, in execution order"
        (is (= 2 (count steps)))
        (is (= parentOf (first (:goal (first steps))))))
      (testing "each step carries the estimate and what was bound when it runs"
        (is (every? #(number? (:est-matches %)) steps))
        (is (= #{} (:bound-before (first steps))))
        (is (contains? (:bound-before (second steps)) '?y)))
      (testing "and the two other numbers the order turned on, on every step"
        (is (every? #(number? (:est-rows %)) steps))
        (is (every? #(number? (:est-prefix %)) steps))
        (is (every? #(= 0 (:block %)) steps) "the two literals share ?y, so one block"))
      (testing "with planning off there are no blocks to be in, and it says so"
        ;; the field is read off the plan that ran; a conjunction returned untouched
        ;; ran no ordering, so it reports none rather than a plausible zero
        (let [flat (unplanned #(plan/explain kb [(list dog '?y) (list parentOf Tom '?y)]
                                             CxPlan))]
          (is (= [(list dog '?y) (list parentOf Tom '?y)] (map :goal flat)))
          (is (every? #(nil? (:block %)) flat))
          (is (not-any? :isolated? flat)))))))

(tu/deftest-kb query-plan-reports-provers-for-a-goal-and-a-join-for-a-conjunction
  (tu/with-terms [parentOf dog Tom Bob Ann CxPlan]
    (v/assert kb (list parentOf Tom Bob) CxPlan)
    (v/assert kb (list dog Bob) CxPlan)
    (v/assert kb (list dog Ann) CxPlan)
    (testing "a single sentence still reports per-prover estimates"
      (let [p (v/query-plan kb (list dog '?y) CxPlan)]
        (is (seq p))
        (is (every? #(contains? % :prover) p))))
    (testing "a vector reports the join plan instead, in execution order"
      (let [p (v/query-plan kb [(list dog '?y) (list parentOf Tom '?y)] CxPlan)]
        (is (= 2 (count p)))
        (is (every? #(contains? % :est-matches) p))
        (is (= parentOf (first (:goal (first p)))))))))

;; ---- the subtype fan ----------------------------------------------------

(defn- hierarchy!
  "A `genl` tree of `depth` levels, `branching` children per node, rooted at `t 0`, with
  one instance per type in the lower half — so `specs` of the root is the whole tree and a
  unary literal on it fans over all of it.  Returns how many types it holds."
  [kb ctx t ind depth branching]
  (let [n (reduce + (take depth (iterate #(* % branching) 1)))]
    (v/assert-many kb
                   (concat (for [i (range 1 n)]
                             (list 'genl (symbol (str t "_" i))
                                   (symbol (str t "_" (quot (dec i) branching)))))
                           (for [i (range (quot n 2) n)]
                             (list (symbol (str t "_" i)) (symbol (str ind "I" i)))))
                   ctx {:chain? false})
    n))

(tu/deftest-kb the-fan-over-a-subtype-closure-is-the-general-walks-own-number
  ;; DECISION (07-join-estimation, and this namespace's "Two estimators"): `est-matches`
  ;; bounds a literal from above, and a reading of 1 is a *proof* it matches at most once
  ;; — `rank-blocks` reads a block of them as a proof the block cannot multiply and
  ;; `cartesian-factors` rests on the same claim.  So reading the subtype roots directly
  ;; instead of walking a built literal per subtype is a constant-factor change and
  ;; nothing else: **equality**, and against the walk itself rather than against a number
  ;; written down here.
  (tu/with-terms [plan_t PlanNode PlanQ CxPlan]
    (let [types (hierarchy! kb CxPlan plan_t PlanNode 5 3)
          typ   (fn [i] (symbol (str plan_t "_" i)))
          ;; the general walk, reached by construction: `prefix-estimate` per subtype, the
          ;; path any argument shape but a bare open variable takes
          ;; the general walk, reached by construction — with `est-matches`' one earlier
          ;; branch in front of it, since a literal with nothing left open is answered as
          ;; a *test* and never reaches the fan at all
          walked (fn [goal bound]
                   (let [[t a] goal
                         ix (:index kb)]
                     (if (#'plan/closed? goal bound)
                       1
                       (min 1000000000
                            (reduce (fn [acc t']
                                      (+ acc (#'plan/prefix-estimate
                                              ix (list t' a) p/count-at)))
                                    0
                                    (tax/specs (reasoning/taxonomy kb) t CxPlan))))))
          est    (fn [goal bound] (plan/est-matches kb goal bound {:context CxPlan}))]
      (testing "the hierarchy is deep enough that the fan is the branch under test"
        (is (< 100 types))
        (is (< (est (list (typ (dec types)) '?x) #{}) (est (list (typ 0) '?x) #{}))))
      (testing "an open atom argument — the form the direct read answers"
        (doseq [i [0 1 (quot types 2) (dec types)]]
          (let [goal (list (typ i) '?x)]
            (is (= (walked goal #{}) (est goal #{})) (str "at " (typ i))))))
      (testing "and the shapes that must still take the walk, because their prefix is deeper"
        (doseq [[goal bound]
                [;; a bound variable: the walk stops on it exactly as on a free one, since
                 ;; a bound token is not a value the prefix can be extended with
                 [(list (typ 0) '?x) '#{?x}]
                 ;; a compound argument: its own tokens extend the prefix past the functor
                 [(list (typ 0) (list PlanQ '?n PlanNode)) #{}]
                 [(list (typ 0) (list PlanQ '?n PlanNode)) '#{?n}]]]
          (is (= (walked goal bound) (est goal bound))
              (str (pr-str goal) " under " (pr-str bound)))))
      (testing "a ground argument never reaches the fan at all — it is a test, and 1"
        (is (= 1 (est (list (typ 0) (symbol (str PlanNode "I" (quot types 2)))) #{}))))
      (testing "and `explain` reports the walk's number for the literal that fans"
        (doseq [gs [[(list (typ 0) '?x) (list PlanQ '?x '?y)]
                    [(list PlanQ '?x '?y) (list (typ 0) '?x)]]]
          (let [row (first (filter #(= (typ 0) (first (:goal %)))
                                   (plan/explain kb gs CxPlan)))]
            (is (some? row) (str "the broad literal is in the plan — " (pr-str gs)))
            (is (= (walked (:goal row) (:bound-before row)) (:est-matches row))
                (pr-str gs))))))))

;; ---- explain costs its report off the plan's own reads --------------------

(tu/deftest-kb explain-reads-the-index-once-for-the-ranking-and-the-report
  ;; `explain` re-costs every literal in execution order to report `:est-matches`,
  ;; `:est-rows` and `:est-prefix`, and a unary type literal's two estimators each read
  ;; `count-at` once per member of its subtype closure.  Those reads go through the
  ;; memoized set the ranking already filled (`memo-opts`), so what the report adds
  ;; over the plan is flat in how wide the hierarchy is — the node engine asks this of
  ;; every enqueued child (`tactics/base-estimate`), where a fan re-read per child is
  ;; the whole of the estimate's cost.
  (tu/with-terms [broad_t rel CxExplain]
    (let [widen! (fn [n]
                   (doseq [_ (range n)]
                     (let [t (tu/tmp-type "pe_sub") x (tu/tmp-ind "PeX")]
                       (v/assert kb (list 'genl t broad_t) CxExplain)
                       (v/assert kb (list t x) CxExplain)
                       (v/assert kb (list rel x x) CxExplain))))
          goals  [(list broad_t '?x) (list rel '?x '?y)]
          reads  (fn [f]
                   (prof/start)
                   (try (f) (finally nil))
                   (reduce + 0 (vals (:reads (prof/stop)))))
          delta  (fn []
                   (- (reads #(doall (plan/explain kb goals CxExplain)))
                      (reads #(plan/order kb goals CxExplain))))]
      (widen! 4)
      (let [narrow (delta)]
        (widen! 12)
        (let [wide (delta)]
          (is (= narrow wide)
              (str "the report's reads over the plan's must not grow with the subtype "
                   "width (" narrow " -> " wide ")")))))))
