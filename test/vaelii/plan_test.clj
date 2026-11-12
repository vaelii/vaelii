;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.plan-test
  "Conjunctive query planning (`vaelii.impl.plan`): the two estimators, the q-error of
  the join model per depth, the block ordering, the fixed placements, and that planning
  changes no answer set.  A cost claim is checked against the rows the engine runs for
  every permutation (`actual-rows`), not against the planner's own predicates.
  See docs/inference.md, \"Conjunctive query planning\"."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; The ranking is forced on whatever the run installed: these tests measure the ranking,
;; which `VAELII_PLAN=0` removes, and forcing it keeps the assertion count identical
;; across configurations (`tu/shipped-fixture`).
(use-fixtures :each (tu/neutral-fresh tu/fresh) (tu/shipped-fixture [#'plan/*enabled*]))

(defn- permutations
  "Every ordering of `coll` as a vector: `prove` reads a vector as a conjunction and a list as one literal."
  [coll]
  (map vec (tu/permutations coll)))

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
  ;; Three facts over two first arguments average 1 per value while Tom matches twice,
  ;; so an average charged to a bound ?x would read below the true match count.
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
        (let [step (first (plan/explain kb [g (list 'lessThan 1 2)] CxPlan {:bound '#{?x}}))]
          (is (< (:est-prefix step) (:est-matches step))
              "the prefix estimate narrows where the per-literal bound does not"))))
    (testing "and a literal with everything bound is a test — one-sided and tight"
      (is (= 1 (plan/est-matches kb (list parentOf '?x '?y) '#{?x ?y}))))))

(tu/deftest-kb an-open-functor-is-costed-by-the-argument-root
  ;; The matcher answers `(?type Muffet)` from the position-1 argument roots, so the
  ;; estimate is that count; the trie stops at the open first token.
  (tu/with-terms [animal dog Muffet Other CxPlan]
    (v/assert kb (list 'genl dog animal) CxPlan)
    (v/assert kb (list dog Muffet) CxPlan)
    (v/assert kb (list animal Other) CxPlan)
    (testing "bounded by the argument root, not by the size of the KB"
      (is (= (reads/stored-count-with-arg-global (:index kb) 1 Muffet)
             (plan/est-matches kb (list '?c Muffet) #{}))))
    (testing "with nothing indexable to lead with, nothing bounds it"
      (is (< (plan/est-matches kb (list '?c Muffet) #{})
             (plan/est-matches kb '(?c ?x) #{}))))
    (testing "a concrete unary functor fans over its subtype closure"
      (is (> (plan/est-matches kb (list animal '?x) #{})
             (plan/est-matches kb (list dog '?x) #{}))))
    (testing "a negated open functor is costed by the same argument root"
      ;; `count-with-functor` answers 0 for a variable
      (is (= (reads/stored-count-with-arg-global (:index kb) 1 Muffet)
             (plan/est-matches kb (list 'not (list '?c Muffet)) #{}))))))

(tu/deftest-kb a-dotted-rest-pattern-is-not-ranked-free
  ;; Both index models answer 0 for a dotted rest, which would rank it cheapest.
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
      ;; the negative arm reaches the argument roots for an open functor
      (is (pos? (plan/est-matches kb (list 'not (list '?p '. '?args)) #{})))
      (is (pos? (plan/est-matches kb (list 'not (list rel '. '?args)) #{}))))
    (testing "so the selective literal still leads, whichever way it was written"
      (let [dotted (list rel '. '?args)
            sel    (list dog '?x)]
        (is (= [sel dotted] (plan/order kb [dotted sel] CxPlan)))
        (is (= [sel dotted] (plan/order kb [sel dotted] CxPlan)))))))

;; ---- the join model: the other estimator --------------------------------

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
      (is (not (contains? (:distinct (plan/est-rows kb (list parentOf '?x '?y))) '?y))))
    (testing "a known leading argument moves the countable column along"
      (is (= {:rows 2 :vars '#{?y} :distinct '{?y 2}}
             (plan/est-rows kb (list parentOf Tom '?y)))))
    (testing "a ground literal has no columns at all, and yields one row or none"
      (is (= {:rows 1 :vars #{} :distinct {}} (plan/est-rows kb (list parentOf Tom Bob))))
      (is (= {:rows 0 :vars #{} :distinct {}} (plan/est-rows kb (list parentOf Bob Tom)))))))

(tu/deftest-kb a-variable-repeated-inside-one-literal-is-a-join-and-is-priced-as-one
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
        ;; 12 rows / 6 distinct leading values
        (is (= 2 (:rows self)))
        (is (< (:rows self) (:rows open))))
      (testing "and no column carries more distinct values than the narrowed relation has rows"
        (is (every? #(<= % (:rows self)) (vals (:distinct self)))))
      (testing "a third occurrence divides again, and the estimate floors at one row"
        ;; a zero would rank the literal below a genuinely empty one
        (is (= 1 (:rows (plan/est-rows kb (list linksTo '?x '?x '?x))))))
      (testing "the upper bound is untouched, because it is a bound and this is not one"
        (is (= 12 (plan/est-matches kb (list linksTo '?x '?x) #{})))))))

(tu/deftest-kb est-rows-reports-rows-and-no-columns-for-the-shapes-the-trie-cannot-walk
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
  (tu/with-terms [animal dog cat Muffet Tom CxPlan]
    (v/assert kb (list 'genl dog animal) CxPlan)
    (v/assert kb (list 'genl cat animal) CxPlan)
    (v/assert kb (list dog Muffet) CxPlan)
    (v/assert kb (list cat Tom) CxPlan)
    (testing "both fan a supertype literal over its subtype closure"
      (is (= 2 (plan/est-matches kb (list animal '?x) #{})))
      (is (= 2 (:rows (plan/est-rows kb (list animal '?x))))))
    (testing "but only est-matches takes the bindings in hand, and it is the bound"
      (is (= 1 (plan/est-matches kb (list animal '?x) '#{?x})))
      (is (= 2 (:rows (plan/est-rows kb (list animal '?x))))))))

(tu/deftest-kb a-genl-read-with-one-end-open-is-priced-at-its-closure-without-a-walk
  ;; A leaf stores no edge into it, and its closure still answers the leaf itself.
  (tu/with-terms [top mid low side CxPlan]
    (doseq [[s g] [[mid top] [low mid] [side top]]]
      (v/assert kb (list 'genl s g) CxPlan))
    (let [tx      (reasoning/taxonomy kb)
          walks   (atom 0)
          [sg gg] [tax/specs-global tax/genls-global]
          price   (fn [goal]
                    (with-redefs [tax/specs-global (fn [t n] (swap! walks inc) (sg t n))
                                  tax/genls-global (fn [t n] (swap! walks inc) (gg t n))]
                      [(plan/est-matches kb goal #{}) (:rows (plan/est-rows kb goal))]))
          answers (fn [goal] (count (set (map #(get % '?v) (v/prove kb [goal] CxPlan)))))]
      (caches/lru-clear! (:closure-lru @tx))
      (testing "an end with no edge in the read direction answers its reflexive row alone"
        (doseq [goal [(list 'genl '?v low) (list 'genl top '?v)]]
          (is (= [1 1] (price goal)) (pr-str goal))
          (is (= 1 (answers goal)) (pr-str goal))))
      (testing "a closure the cache does not hold is bounded by the relation's active edges"
        (let [[em rows] (price (list 'genl '?v top))]
          (is (= (inc (tax/active-edge-count tx :genl)) em))
          (is (= 3 rows) "the two stored edges into top and the reflexive row")))
      (testing "a closure the join has read prices at its size"
        (sg tx top)
        (gg tx low)
        (is (= [4 4] (price (list 'genl '?v top))))
        (is (= 4 (answers (list 'genl '?v top))))
        (is (= [3 3] (price (list 'genl low '?v))))
        (is (= 3 (answers (list 'genl low '?v)))))
      (is (zero? @walks) "no price reads a closure through the taxonomy"))))

(defn- forward-join-order
  "The literals a forward join of `(implies (and (goes ?t) (selects ?t ?g) (memberOf ?g ?x)
  (wide ?x)) (out ?x))` takes, in order, by functor, with `replan` standing for
  `chain/replanned`; and whether the rule concludes `out` of the one member of `Narrow`.  The
  one `selects` row binds `?g` to `Narrow`, which has one member, and `Big` has thirty."
  [kb replan]
  (tu/with-terms [goes selects memberOf wide out T Narrow Big CxPlan]
    (let [ws     (mapv #(tu/tmp-ind (str "W" %)) (range 6))
          bs     (mapv #(tu/tmp-ind (str "B" %)) (range 30))
          join   @#'chain/join-antecedent
          joined (atom [])]
      (doseq [f (concat [(list goes T) (list selects T Narrow) (list memberOf Narrow (first ws))]
                        (map #(list memberOf Big %) bs)
                        (map #(list wide %) ws))]
        (v/assert kb f CxPlan))
      (with-redefs-fn {#'chain/join-antecedent (fn [kb ante & args]
                                                 (swap! joined conj ante)
                                                 (apply join kb ante args))
                       #'chain/replanned       replan}
        #(v/assert kb (list 'implies (list 'and (list goes '?t) (list selects '?t '?g)
                                           (list memberOf '?g '?x) (list wide '?x))
                            (list out '?x))
                   CxPlan {:direction :forward}))
      [(into [] (keep #({goes :goes selects :selects memberOf :member wide :wide} (first %))) @joined)
       (= [{'?x (first ws)}] (v/query kb [(list out '?x)] CxPlan))])))

(tu/deftest-kb a-forward-join-re-plans-the-literals-left-at-the-values-of-its-one-row
  (let [[first-plan concl-first] (forward-join-order kb (fn [_ more _ _] more))
        [replanned concl]        (forward-join-order kb @#'chain/replanned)
        before                   #(< (.indexOf ^java.util.List %1 :member) (.indexOf ^java.util.List %1 :wide))]
    (testing "the first plan, with ?g bound to no value yet, joins memberOf after wide"
      (is (not (before first-plan)) (pr-str first-plan)))
    (testing "once selects leaves one row, memberOf is priced at Narrow's one member and leads"
      (is (before replanned) (pr-str replanned)))
    (is (and concl-first concl) "both orders conclude out of Narrow's one member")))

(tu/deftest-kb the-counts-span-every-context-and-a-read-is-scoped-to-one
  (tu/with-terms [parentOf Tom Bob Cid CxTop CxSub]
    (v/assert kb (list 'genlCx CxSub CxTop) 'CxUniverse
              {:strength :monotonic})
    (doseq [c [CxTop CxSub]]
      (v/assert kb (list parentOf Tom Bob) c {:strength :monotonic}))
    (v/assert kb (list parentOf Tom Cid) CxTop {:strength :monotonic})
    (let [goal (list parentOf Tom '?y)
          seen (fn [c] (count (v/sentexes-matching kb goal c)))]
      (testing "the bound stays sound, which is the property everything rests on"
        (is (<= (seen CxTop) (plan/est-matches kb goal #{} {:context CxTop})))
        (is (<= (seen CxSub) (plan/est-matches kb goal #{} {:context CxSub})))
        (is (= (plan/est-matches kb goal #{} {:context CxTop})
               (plan/est-matches kb goal #{} {:context CxSub}))
            "and it is the same number in both, the counts being context-blind"))
      (testing "the inflation lands on the rows and not on the columns"
        (let [r (plan/est-rows kb goal)]
          (is (= 3 (:rows r)) "(Tom Bob) twice over and (Tom Cid) once")
          (is (= {'?y 2} (:distinct r)) "but Bob and Cid are two values, not three")
          (is (> (:rows r) (seen CxTop)))))
      (testing "a ground literal is clamped, so the multiplicity cannot reach it"
        (is (= 1 (:rows (plan/est-rows kb (list parentOf Tom Bob)))))
        (is (= 1 (plan/est-matches kb (list parentOf Tom Bob) #{})))))))

(deftest a-join-divides-by-the-side-that-can-count-the-variable
  ;; The formula away from any index (docs/inference.md, "Composing them").
  (let [join #'plan/join-summary]
    (testing "the counted side decides"
      (is (= 40.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 20.0}}
                               {:rows 20.0 :vars '#{?b ?c} :distinct '{?b 10.0}})))))
    (testing "with nothing read anywhere there is nothing to divide by, and it is a product"
      (is (= 400.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct {}}
                                {:rows 20.0 :vars '#{?b ?c} :distinct {}})))))
    (testing "but a side that read *some* column lends it as a proxy for one it did not"
      (is (= 40.0 (:rows (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 10.0}}
                               {:rows 20.0 :vars '#{?b ?c} :distinct '{?c 20.0}})))))
    (testing "and the proxy is the smaller of the two, a guess erring towards a larger join"
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
      (let [ab   (join {:rows 20.0 :vars '#{?a ?b} :distinct '{?a 20.0}}
                       {:rows 20.0 :vars '#{?b ?c} :distinct '{?b 10.0 ?c 5.0}})
            next {:rows 10.0 :vars '#{?c ?d} :distinct '{?c 5.0}}]
        (is (= 40.0 (:rows ab)))
        (is (= '{?a 20.0 ?b 10.0 ?c 5.0} (:distinct ab)))
        (is (= 80.0 (:rows (join ab next))))
        ;; against a side that cannot read ?c: without the propagated reading the join
        ;; falls back on the proxy, and without the proxy it is a product
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
  "The model's expected prefix size against the count the engine returns for that
  prefix, per join depth: `q = max(est/actual, actual/est)`."
  [kb goals ctx]
  (let [steps (plan/explain kb goals ctx)
        order (mapv :goal steps)]
    (mapv (fn [k]
            (let [est (double (max 1 (:est-prefix (nth steps (dec k)))))
                  act (double (max 1 (unplanned #(count (v/prove kb (vec (take k order)) ctx)))))]
              (max (/ est act) (/ act est))))
          (range 1 (inc (count order))))))

(tu/deftest-kb the-join-estimate-is-exact-on-a-uniform-chain-at-every-depth
  ;; Arguments independent and fan-out uniform: the model's assumption holds.
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

(tu/deftest-kb the-join-estimate-stays-bounded-when-the-assumption-is-false
  ;; One hub value takes three quarters of the first relation, and the other two
  ;; relations' fan-outs vary with the join key: a joint distribution per-position counts
  ;; cannot see.  q reads 1.00, 2.75, 3.28 (docs/inference.md).
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
        ;; an error multiplying per join would read q3 ≈ q2²
        (is (< q3 (* 1.5 q2)) (str "q went " q2 " -> " q3)))
      (testing "and the plan is a function of the conjunction, not of how it was written"
        (is (= (mapv :goal (plan/explain kb goals CxPlan))
               (mapv :goal (plan/explain kb (vec (reverse goals)) CxPlan))))))))

(tu/deftest-kb the-bound-variables-are-a-one-row-relation-and-nothing-special
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
    ;; three subtypes, so the hierarchy literal is dearer than Muffet's memberships
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
  `loose` relation of `few` facts sharing no variable with them: the smallest extent,
  which a cheapest-first pick would put first."
  [kb ctx [link1 link2 link3 loose Node] n few]
  (let [node (fn [p i] (symbol (str Node p i)))]
    (v/assert-many kb
                   (concat (for [i (range n)] (list link1 (node "A" i) (node "B" i)))
                           (for [i (range n)] (list link2 (node "B" i) (node "C" i)))
                           (for [i (range n)] (list link3 (node "C" i) (node "D" i)))
                           (for [i (range few)] (list loose (node "U" i) (node "V" i))))
                   ctx {:chain? false})))

(defn- actual-rows
  "The sum over k of the engine's solution count for the order's first k literals,
  run unplanned: the intermediate rows the order passes through."
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
          (is (:isolated? (last rows)))
          (is (< (:est-matches (last rows)) (:est-matches (first rows)))))))))

(tu/deftest-kb at-two-literals-the-cheaper-one-leads-and-that-is-already-optimal
  ;; At two literals both orders end on the same join, so the costs differ only by the
  ;; leading literal's own extent.
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
      (testing "no permutation runs fewer rows"
        (let [planned (plan/order kb conjuncts CxPlan)
              costs   (map #(actual-rows kb % CxPlan) (permutations conjuncts))]
          (is (= (actual-rows kb planned CxPlan) (apply min costs)))))
      (testing "and the cartesian factor is last however the conjunction was written"
        ;; the chain literals have equal extents, so their order follows written order
        (doseq [p (permutations conjuncts)]
          (is (= (list loose '?u '?v) (last (plan/order kb p CxPlan)))))))))

(defn- random-trial!
  "One randomized join: four relations of a few facts each, named per trial from the
  gensym'd bases, and one literal on each over a small variable pool.  Returns the
  conjunction."
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
  "The conjuncts that carry a variable and share none with any other conjunct, computed
  here rather than read off the planner.  A ground conjunct satisfies the sharing test
  vacuously, hence the first clause."
  [conjuncts]
  (let [vars  (fn [l] (set (filter #(and (symbol? %) (.startsWith (name %) "?"))
                                   (tree-seq sequential? seq l))))
        counts (frequencies (mapcat (comp seq vars) conjuncts))]
    (set (filter #(and (seq (vars %))
                       (every? (fn [v] (= 1 (counts v))) (vars %)))
                 conjuncts))))

(tu/deftest-kb planning-changes-no-answers-over-randomized-conjunctions
  ;; A corpus small enough for an exhaustive answer check, and too small for a cost
  ;; claim, which the oracle test below makes.
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
  "One randomized four-way join: relations of 15–60 facts, large enough that a ratio
  between two orders' rows is not integer granularity, and one literal on each over a
  small variable pool."
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
  ;; An oracle: all twenty-four permutations, costed by the engine.  The claim is on the
  ;; totals, which weight a trial by the rows it ran; a mean of per-trial ratios is
  ;; dominated by the trial with the smallest oracle.  At this seed the totals read 4.8%
  ;; above the best (docs/inference.md).
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
        (is (every? #(<= (* 2 (:planned %)) (+ (:best %) (:worst %))) trials)
            (pr-str (remove #(<= (* 2 (:planned %)) (+ (:best %) (:worst %))) trials)))))))

(defn- fan-kb!
  "A chain of `linkOne`/`linkTwo`, 20 rows joining to 80."
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
  ;; The shape both chaining paths hand the planner once a trigger's bindings are
  ;; substituted in (`chain/planned-join`, `res/planned-antecedents`).
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
        (let [steps (plan/explain kb written CxPlan)]
          (is (= [0 1 1] (map :block steps)))
          (is (= 0 (:est-rows (first steps)))))))))

(tu/deftest-kb an-est-override-replaces-the-index-model-and-counts-no-columns
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
        (let [[a b :as steps] (plan/explain kb [w n] CxPlan {:est-override huge})]
          (is (= [n w] (mapv :goal steps)))
          (is (= 5000 (:est-matches b)) "the overridden literal reports what it was costed at")
          (is (= 5000 (:est-rows b)))
          (is (= (plan/est-matches kb n #{}) (:est-matches a))
              "and one the override declines to answer falls back on the index model")
          (is (= (:rows (plan/est-rows kb n)) (:est-rows a))))
        ;; an override counts no column, so the prefix is the product of its rows
        (let [flat  (fn [_ _] 7)
              steps (plan/explain kb [w n] CxPlan {:est-override flat})]
          (is (every? #(= 7 (:est-matches %)) steps))
          (is (= [7 49] (mapv :est-prefix steps))))
        (testing "explain asks the override nothing about a deferred literal"
          (let [steps (plan/explain kb [w (list 'lessThan '?s 5)] CxPlan
                                    {:est-override (fn [_ _] 7)})]
            (is (= [7 1] (mapv :est-matches steps)))))))))

(tu/deftest-kb an-unshared-literal-that-cannot-fan-out-leads-too
  ;; `loose` shares no variable, and an `est-matches` of 1 proves it cannot multiply.
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
        ;; the transposition law leads with it against the fanning chain, and nothing
        ;; was held back
        (v/assert kb (list loose (symbol (str Node "U1")) (symbol (str Node "V1")))
                  CxPlan)
        (is (= 2 (plan/est-matches kb lo #{})))
        (is (= [lo c1 c2] (plan/order kb written CxPlan)))
        (is (< (actual-rows kb [lo c1 c2] CxPlan)
               (actual-rows kb [c1 c2 lo] CxPlan)))
        (is (not-any? :isolated? (plan/explain kb written CxPlan)))))))

(tu/deftest-kb a-cartesian-factor-changes-places-where-the-transposition-law-says-it-does
  ;; The chain's `s/(n−1)` is 100/79 ≈ 1.27; a disconnected relation of `m` rows reads
  ;; `m/(m−1)`, above that at four rows and below it at five.
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
  ;; A pair sharing a variable with each other and with nothing else is a cartesian
  ;; factor, and neither literal is isolated.  The small pair belongs in front.
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
        (is (not-any? :isolated? steps)))
      (testing "the small block leads, and that is the cheapest order of the twenty-four"
        (is (= [s1 s2] (take 2 planned)))
        (is (= (actual-rows kb planned CxPlan)
               (apply min (map #(actual-rows kb % CxPlan) (permutations written))))))
      (testing "and interleaving the two blocks costs more, which is why they moved together"
        (is (< (actual-rows kb planned CxPlan)
               (actual-rows kb [s1 b1 s2 b2] CxPlan)))))))

(tu/deftest-kb a-block-the-caller-already-narrowed-runs-before-one-it-did-not
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

(tu/deftest-kb a-block-that-cannot-multiply-runs-before-the-anchored-block
  (tu/with-terms [known guard Node CxPlan]
    (v/assert-many kb (for [i (range 12)]
                        (list known (symbol (str Node "K" (mod i 4))) (symbol (str Node "L" i))))
                   CxPlan {:chain? false})
    (let [anchored (list known '?k '?l)
          g        (list guard (symbol (str Node "Zed")))]
      (is (= [g anchored] (plan/order kb [anchored g] CxPlan {:bound '#{?k}}))))))

(tu/deftest-kb a-literal-feeding-an-evaluable-is-not-a-cartesian-factor
  ;; `age` shares a variable only with the evaluable, so sharing is judged against the
  ;; deferred literals too (the anchored block).
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
        (is (= 'lessThan (first (nth ordered 1))))))
    (testing "explain passes the prefix through a deferred literal unchanged"
      ;; the trie answers 0 for `evaluate`, so reading it would zero the prefix
      (let [[a b] (plan/explain kb [(list age '?p '?n) (list 'evaluate '?z (list '+ '?n 1))]
                                CxPlan)]
        (is (= (:est-prefix a) (:est-prefix b)))))))

(tu/deftest-kb the-recursive-literal-stays-last-so-recursion-still-terminates
  (tu/with-terms [parentOf ancestorOf Aa Bb Cc Dd CxPlan]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) CxPlan {:direction :forward})
    (v/assert-rule kb [(list parentOf '?x '?y) (list ancestorOf '?y '?z)]
                   (list ancestorOf '?x '?z) CxPlan {:direction :forward})
    (doseq [[p c] [[Aa Bb] [Bb Cc] [Cc Dd]]]
      (v/assert kb (list parentOf p c) CxPlan))
    (testing "the literal sharing the consequent's functor is placed last"
      (let [ordered (plan/order kb [(list ancestorOf '?y '?z) (list parentOf '?x '?y)]
                                CxPlan {:consequent-pred ancestorOf})]
        (is (= parentOf   (first (first ordered))))
        (is (= ancestorOf (first (second ordered))))))
    (testing "so a right-recursive rule still terminates and closes transitively"
      (is (= #{Bb Cc Dd}
             (set (map #(get % '?who)
                       (v/prove kb (list ancestorOf Aa '?who) CxPlan))))))))

(tu/deftest-kb a-waiting-literal-follows-its-binder-with-the-ranking-on-or-off
  ;; `edge` is the cheapest literal, so only the readiness discipline moves it behind
  ;; `pairOf`, which binds ?a.  `tag` is dearer than `pairOf` and runs after it, so the
  ;; waiting literal is placed between two generators.
  (tu/with-terms [edge pairOf tag score has Aa Bb Cc Dd CxPlan]
    (v/assert kb (list edge Aa Bb) CxPlan)
    (doseq [[x y] [[Aa Bb] [Bb Cc] [Cc Aa]]] (v/assert kb (list pairOf x y) CxPlan))
    (doseq [c [Aa Bb Cc Dd]] (v/assert kb (list tag c) CxPlan))
    (v/assert kb (list has Aa 3) CxPlan)
    (let [e        (list edge '?a '?b)
          p        (list pairOf '?a '?c)
          t        (list tag '?c)
          ends     (fn [l] (when (= edge (first l)) '#{?a ?b}))
          s        (list score '?n)
          h        (list has '?x '?n)
          computed (fn [g bnd] (when (= score (first g)) (if (bnd '?n) 1 plan/unbounded)))]
      (doseq [ranked? [true false]]
        (binding [plan/*enabled* ranked?]
          (testing (str "an :end-vars literal runs right after the generator binding an end, ranked " ranked?)
            (is (= [p e t] (plan/order kb [e p t] CxPlan {:end-vars ends})))
            (is (= e (first (plan/order kb [e p t] CxPlan))) "without :end-vars it leads"))
          (testing (str "a literal the override costs at unbounded follows its binder, ranked " ranked?)
            (is (= [h s] (plan/order kb [s h] CxPlan {:est-override computed}))))))
      (testing "unranked, an :end-vars literal no generator can bind keeps its place"
        (is (= [e s] (binding [plan/*enabled* false]
                       (plan/order kb [e s] CxPlan {:end-vars ends}))))))))

(tu/deftest-kb a-computed-literal-follows-its-binder-however-many-variables-it-shares-with-the-prefix
  ;; `apart` shares five variables with `rowOf`, and its override summary counts no
  ;; column, so its join onto `rowOf` divides `unbounded` by the guessed distinct count
  ;; five times and estimates fewer rows than `mark`'s cross product.
  (tu/with-terms [rowOf apart mark Node CxPlan]
    (v/assert-many kb (concat (for [i (range 32)] (list rowOf (symbol (str Node "A" i)) Node Node Node Node))
                              (for [j (range 40)] (list mark (symbol (str Node "E" j)))))
                   CxPlan {:chain? false})
    (let [r (list rowOf '?a '?b '?c '?d '?f)
          a (list apart '?a '?b '?c '?d '?f '?e)
          m (list mark '?e)
          computed (fn [g bnd] (when (= apart (first g)) (if (every? bnd (rest g)) 1 plan/unbounded)))]
      (doseq [ranked? [true false], written (permutations [r a m])]
        (binding [plan/*enabled* ranked?]
          (is (= a (last (plan/order kb written CxPlan {:est-override computed})))
              (pr-str ranked? written)))))))

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
  ;; A rule's antecedents, planned by `res/planned-antecedents`.
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
  ;; `res/prove` computes a deferred conjunct through the registry (`res/solve-deferred`).
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
  ;; `count-at`, `count-children` and `count-with-functor` take an index and one
  ;; argument; `count-with-arg` takes a position as well.
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
  ;; The direct read of the subtype roots must equal the general walk exactly: a
  ;; reading of 1 is the proof `rank-blocks` ranks a block on.
  (tu/with-terms [plan_t PlanNode PlanQ CxPlan]
    (let [types (hierarchy! kb CxPlan plan_t PlanNode 5 3)
          typ   (fn [i] (symbol (str plan_t "_" i)))
          ;; `prefix-estimate` per subtype, behind `est-matches`' settled-literal branch
          walked (fn [goal bound]
                   (let [[t a] goal
                         ix (:index kb)]
                     (if (#'plan/settled-when-run? goal bound)
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
                [;; a bound variable: the walk stops on it as on a free one
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
  ;; `explain` reads through the memoized set the ranking filled (`memo-opts`), so its
  ;; reads beyond the plan's do not grow with the subtype closure's width.  The node
  ;; engine asks this of every enqueued child (`tactics/base-estimate`).
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
