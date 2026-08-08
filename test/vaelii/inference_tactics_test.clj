;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inference-tactics-test
  "The node engine's ordering **policy** (`vaelii.impl.tactics`): the four-term estimate,
  the tactician sign table, the child bias, and the two opt-in modes.

  One test here is the contract and the rest are diagnosis:
  `every-complete-tactician-returns-the-same-answers`.  Ordering is a cost decision and
  never a semantic one, so a tactician that answers differently is a tactician that
  dropped a node — and the sweep is what says so before anyone ships it."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inf]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.tactics :as tac]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- answers
  "Every solution the node engine finds for `goals` under `strat`, as a set."
  ([kb goals context strat] (answers kb goals context strat 5))
  ([kb goals context strat depth]
   (set (inf/solutions kb goals context {:strategy strat :max-depth depth}))))

(defn- node
  "A hand-built node, for asking the estimate about one shape rather than about a search."
  ([context literals] (node context literals 0))
  ([context literals tree-depth]
   {:literals   (mapv (fn [[s d]] {:sentence s :depth d}) literals)
    :from       0
    :sigma      {}
    :guards     []
    :supports   #{}
    :tree-depth tree-depth
    :query-vars #{}
    :context    context}))

(defn- pop-order
  "The nodes `sess` pops, in order, driven dry.  The frontier's decisions, as data."
  [sess]
  (loop [acc []]
    (if-let [[_ id] (first @(:queue sess))]
      (let [n (get @(:nodes sess) id)]
        (inf/step! sess)
        (recur (conj acc n)))
      acc)))

(defn- branching-kb!
  "Two rules concluding `anc` — one hop, one recursive — over a four-node chain, plus a
  diamond into `reach`.  Several derivations at several depths, which is what a
  completeness sweep needs to have anything to disagree about."
  [kb edgeOf anc reach mid1 mid2 context inds]
  (doseq [[a b] (partition 2 1 inds)]
    (v/assert kb (list edgeOf a b) context))
  (v/assert-rule kb [(list edgeOf '?x '?y)] (list anc '?x '?y) context
                 {:direction :backward})
  (v/assert-rule kb [(list edgeOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z) context
                 {:direction :backward})
  (v/assert-rule kb [(list anc '?x '?y)] (list mid1 '?x '?y) context {:direction :backward})
  (v/assert-rule kb [(list anc '?x '?y)] (list mid2 '?x '?y) context {:direction :backward})
  (v/assert-rule kb [(list mid1 '?x '?y)] (list reach '?x '?y) context {:direction :backward})
  (v/assert-rule kb [(list mid2 '?x '?y)] (list reach '?x '?y) context {:direction :backward}))

;; ---- the base term -------------------------------------------------------

(tu/deftest-kb the-base-term-is-the-plan-the-query-would-run
  ;; One cost model, two readers.  A node ordering that disagreed with the join plan it
  ;; is about to run would be a cost model arguing with itself.
  (tu/with-terms [dog parentOf BaseContext]
    (tu/with-terms [BsTom BsRex BsMuffet]
      (v/assert kb (list dog BsRex) BaseContext)
      (v/assert kb (list dog BsMuffet) BaseContext)
      (v/assert kb (list parentOf BsTom BsRex) BaseContext)
      (let [goals [(list dog '?y) (list parentOf BsTom '?y)]
            n     (node BaseContext (mapv #(vector % 3) goals))]
        (doseq [strat [(tac/strategy nil) (tac/strategy :cost)]]
          (is (= (reduce + (map :est-matches (v/query-plan kb goals BaseContext)))
                 (tac/base-estimate kb n BaseContext strat))
              "the base term and query-plan must read the same numbers"))
        (testing "and under :cost — signs at zero — the estimate is that plus the size penalty"
          (let [strat (tac/strategy :cost)]
            (is (= (+ (tac/base-estimate kb n BaseContext strat)
                      (* (:size-penalty strat) 2))
                   (tac/estimate kb strat n)))))
        (testing "the default adds its depth term to the same base"
          (let [strat (tac/strategy nil)]
            (is (= (+ (tac/base-estimate kb n BaseContext strat)
                      (* (:size-penalty strat) 2)
                      (* (:depth-weight strat) 6))          ; two literals at depth 3
                   (tac/estimate kb strat n)))))))))

(tu/deftest-kb a-shorter-conjunction-sorts-ahead-of-a-longer-one-at-equal-cost
  (tu/with-terms [pOne pTwo SizeContext]
    (tu/with-terms [SzInd]
      (v/assert kb (list pOne SzInd) SizeContext)
      (v/assert kb (list pTwo SzInd) SizeContext)
      (let [strat (tac/strategy nil)
            one   (node SizeContext [[(list pOne '?x) 3]])
            two   (node SizeContext [[(list pOne '?x) 3] [(list pTwo '?x) 3]])]
        (is (< (tac/estimate kb strat one) (tac/estimate kb strat two))
            "two literals must sort after one")))))

;; ---- the sign table ------------------------------------------------------

(tu/deftest-kb the-sign-table-is-the-whole-tactician
  (is (= #{:cost :budget-first :ground-first :breadth-first :depth-first
           :removal-first :transformation-first}
         (set (keys tac/tacticians))))
  (is (= :ground-first (:tactician (tac/strategy nil)))
      "the default is the measured one, not the identity one")
  (is (= (tac/strategy nil) (tac/strategy :ground-first)))
  (is (zero? (:depth-sign (tac/strategy :cost))) ":cost must stay the identity policy")
  (testing "a named tactician may still have one term bent"
    (is (= -1 (:depth-sign (tac/strategy {:tactician :cost :depth-sign -1})))))
  (testing "an unknown one is refused rather than silently ordered by nothing"
    (is (= :unknown-tactician
           (:type (try (tac/strategy :nonesuch) (catch clojure.lang.ExceptionInfo e (ex-data e))))))))

(tu/deftest-kb ^:slow every-complete-tactician-returns-the-same-answers
  ;; The gate.  Every tactician reorders the frontier and none of them drops a node, so
  ;; the answer set is the same seven times over; only the order of arrival differs.
  (tu/with-terms [edgeOf anc reach mid1 mid2 SweepContext]
    (tu/with-terms [SwA SwB SwC SwD]
      (branching-kb! kb edgeOf anc reach mid1 mid2 SweepContext [SwA SwB SwC SwD])
      (doseq [goals [[(list anc '?x '?z)]
                     [(list anc SwA '?z)]
                     [(list reach '?x '?z)]
                     [(list anc '?x '?y) (list anc '?y '?z)]]]
        (let [baseline (answers kb goals SweepContext :cost)]
          (is (seq baseline) (str "nothing to compare for " goals))
          (doseq [t (keys tac/tacticians)]
            (is (= baseline (answers kb goals SweepContext t))
                (str t " disagreed with :cost about " goals)))
          (testing "and a bent weight is still the same search"
            (is (= baseline (answers kb goals SweepContext
                                     {:tactician :budget-first :breadth-bias 4.0})))
            (is (= baseline (answers kb goals SweepContext
                                     {:tactician :cost :size-penalty 250})))))))))

(tu/deftest-kb the-frontier-pops-in-the-order-the-signs-imply
  (tu/with-terms [edgeOf anc reach mid1 mid2 OrderContext]
    (tu/with-terms [OrA OrB OrC]
      (branching-kb! kb edgeOf anc reach mid1 mid2 OrderContext [OrA OrB OrC])
      (let [goals [(list reach '?x '?z)]
            order (fn [t] (mapv :tree-depth
                                (pop-order (inf/session kb goals OrderContext
                                                        {:strategy t :max-depth 4}))))
            bf    (order :breadth-first)
            df    (order :depth-first)]
        (is (= bf (vec (sort bf))) ":breadth-first must pop in level order")
        (is (not= df (vec (sort df))) ":depth-first must not")
        (is (< (.indexOf ^java.util.List df (apply max df))
               (.indexOf ^java.util.List bf (apply max bf)))
            ":depth-first must reach the deepest node before :breadth-first does")))))

(tu/deftest-kb flipping-the-depth-sign-changes-the-order-and-not-the-results
  (tu/with-terms [edgeOf anc reach mid1 mid2 SignContext]
    (tu/with-terms [SgA SgB SgC]
      (branching-kb! kb edgeOf anc reach mid1 mid2 SignContext [SgA SgB SgC])
      (let [goals [(list reach '?x '?z)]
            ids   (fn [t] (mapv :id (pop-order (inf/session kb goals SignContext
                                                            {:strategy t :max-depth 4}))))]
        (is (not= (ids :budget-first) (ids :ground-first)) "the sign decided nothing")
        (is (= (answers kb goals SignContext :budget-first 4)
               (answers kb goals SignContext :ground-first 4)))))))

(tu/deftest-kb breadth-bias-scales-the-depth-term-and-nothing-else
  (tu/with-terms [pBias BiasContext]
    (tu/with-terms [BiInd]
      (v/assert kb (list pBias BiInd) BiasContext)
      (let [n    (node BiasContext [[(list pBias '?x) 3]] 2)
            flat (tac/estimate kb (tac/strategy :cost) n)
            one  (tac/estimate kb (tac/strategy {:tactician :ground-first}) n)
            two  (tac/estimate kb (tac/strategy {:tactician :ground-first :breadth-bias 2.0}) n)]
        (is (= (- one flat) (- two one)) "doubling the bias must double the depth term")
        (is (= flat (tac/estimate kb (tac/strategy {:tactician :ground-first
                                                    :breadth-bias 0.0}) n))
            "a zero bias must leave the depth term out entirely")))))

;; ---- the child bias ------------------------------------------------------

(defn- productive-kb!
  "A goal a stored fact answers *and* a rule concludes — so the root is productive and
  still has children, which is what the child bias is a decision about."
  [kb edgeOf anc context a b c d]
  (v/assert kb (list anc a b) context)
  (v/assert kb (list edgeOf c d) context)
  (v/assert-rule kb [(list edgeOf '?x '?y)] (list anc '?x '?y) context
                 {:direction :backward}))

(tu/deftest-kb a-productive-nodes-children-carry-the-tacticians-bias
  (tu/with-terms [edgeOf anc GateContext]
    (tu/with-terms [GtA GtB GtC GtD]
      (productive-kb! kb edgeOf anc GateContext GtA GtB GtC GtD)
      (let [goals [(list anc '?x '?y)]
            after (fn [t] (let [s (inf/session kb goals GateContext
                                               {:strategy t :max-depth 3})]
                            (is (seq (inf/step! s)) "the root produced nothing to bias on")
                            (mapv first @(:queue s))))
            flat  (after :cost)
            sunk  (after :removal-first)
            up    (after :transformation-first)]
        (is (seq flat) "the root built no children to bias")
        (is (every? #(< % (:motivation-weight tac/defaults)) flat)
            "an opinionless tactician must not bias")
        (is (> (apply min sunk) (apply max flat))
            ":removal-first must sink a paying node's children behind the whole frontier")
        (is (< (apply max up) (apply min flat))
            ":transformation-first must hoist them above it")
        (testing "and sinking is not dropping"
          (is (= (answers kb goals GateContext :cost 3)
                 (answers kb goals GateContext :removal-first 3)
                 (answers kb goals GateContext :transformation-first 3))))))))

(tu/deftest-kb first-result-mode-stops-the-frontier-growing-and-says-so
  ;; The one strategy that returns fewer answers.  It is excluded from the completeness
  ;; sweep by name, and this is the test that keeps the exclusion honest.
  (tu/with-terms [edgeOf anc FirstContext]
    (tu/with-terms [FsA FsB FsC FsD]
      (productive-kb! kb edgeOf anc FirstContext FsA FsB FsC FsD)
      (let [goals [(list anc '?x '?y)]
            sess  (inf/session kb goals FirstContext
                               {:strategy {:first-result? true} :max-depth 3})
            sols  (set (doall (inf/search-seq sess)))
            whole (answers kb goals FirstContext :cost 3)]
        (is (false? (tac/complete? (tac/strategy {:first-result? true}))))
        (is (true? (tac/complete? (tac/strategy :cost))))
        (is (zero? (:frontier (inf/tree-stats sess))) "the search did not drain")
        (is (= 1 (:expanded (inf/tree-stats sess)))
            "a productive node must build no children at all")
        (is (seq sols))
        (is (set/subset? sols whole))
        (is (not= sols whole) "the mode that reduces the answer set did not reduce it")))))

;; ---- the backchain estimate ---------------------------------------------

(defn- rule-only-kb!
  "`derived` has no stored facts and two rules concluding it — one over a single-fact
  predicate, one over a three-fact predicate.  The index costs it at zero, which is the
  whole reason `backchain-estimate` exists."
  [kb base other derived context inds]
  (v/assert kb (list base (first inds)) context)
  (doseq [i (take 3 inds)] (v/assert kb (list other i) context))
  (v/assert-rule kb [(list base '?x)] (list derived '?x) context {:direction :backward})
  (v/assert-rule kb [(list other '?x)] (list derived '?x) context {:direction :backward}))

(tu/deftest-kb a-backchain-estimate-costs-a-goal-by-the-rules-that-conclude-it
  (tu/with-terms [base other derived BcContext]
    (tu/with-terms [BcOne BcTwo BcThree]
      (rule-only-kb! kb base other derived BcContext [BcOne BcTwo BcThree])
      (let [g (list derived '?x)]
        (is (zero? (plan/est-matches kb g #{} {:context BcContext}))
            "the index must cost a rule-only predicate at nothing")
        (is (= 1 (tac/backchain-estimate kb g BcContext {}))
            "the cheapest route is the one-fact rule")
        (testing "a goal no rule concludes has no backchain estimate at all"
          (is (nil? (tac/backchain-estimate kb (list base '?x) BcContext {}))))
        (testing "and neither has a deferred literal, or an exhausted depth"
          (is (nil? (tac/backchain-estimate kb (list 'different '?x '?y) BcContext {})))
          (is (nil? (tac/backchain-estimate kb g BcContext {:depth 0}))))))))

(tu/deftest-kb first-takes-the-cheapest-route-and-all-pays-for-every-one
  (tu/with-terms [base other derived AggContext]
    (tu/with-terms [AgOne AgTwo AgThree]
      (rule-only-kb! kb base other derived AggContext [AgOne AgTwo AgThree])
      (let [g (list derived '?x)]
        (is (= 1 (tac/backchain-estimate kb g AggContext {:aggregate :first}))
            ":first is the min — any one rule suffices")
        (is (= 4 (tac/backchain-estimate kb g AggContext {:aggregate :all}))
            ":all is the sum — a complete search runs every candidate")))))

(tu/deftest-kb the-backchain-estimate-reorders-what-the-index-would-rank-backwards
  (tu/with-terms [base other derived RankContext]
    (tu/with-terms [RkOne RkTwo RkThree]
      (rule-only-kb! kb base other derived RankContext [RkOne RkTwo RkThree])
      (let [cheap  (node RankContext [[(list base '?x) 3]])       ; one stored fact
            rulely (node RankContext [[(list derived '?x) 3]])    ; no stored facts at all
            off    (tac/strategy :cost)
            on     (tac/strategy {:estimate-backchain? :all})]
        (is (< (tac/estimate kb off rulely) (tac/estimate kb off cheap))
            "the index ranks the rule-only literal as the cheapest thing in the KB")
        (is (> (tac/estimate kb on rulely) (tac/estimate kb on cheap))
            "costing it through its rules must put it back where it belongs")
        (testing "and a literal with no allowance left is not asked"
          (is (= (tac/estimate kb off (node RankContext [[(list derived '?x) 0]]))
                 (tac/estimate kb on (node RankContext [[(list derived '?x) 0]])))))))))

(tu/deftest-kb the-backchain-estimate-terminates-on-a-cyclic-rule-set
  (tu/with-terms [pingOf pongOf CycEstContext]
    (tu/with-terms [CeInd]
      (v/assert kb (list pongOf CeInd) CycEstContext)
      (v/assert-rule kb [(list pongOf '?x)] (list pingOf '?x) CycEstContext
                     {:direction :backward})
      (v/assert-rule kb [(list pingOf '?x)] (list pongOf '?x) CycEstContext
                     {:direction :backward})
      (is (number? (tac/backchain-estimate kb (list pingOf '?x) CycEstContext {:depth 12}))
          "a repeated goal must cap the recursion, not deepen it")
      (testing "and a whole search under it still answers"
        (is (= #{{'?x CeInd}}
               (answers kb [(list pingOf '?x)] CycEstContext
                        {:estimate-backchain? :first} 3)))))))

;; ---- the portfolio -------------------------------------------------------

(tu/deftest-kb the-portfolios-union-is-each-racers-own-answer-set
  ;; A portfolio is a bet that one ordering finds the answer sooner, never a way to find
  ;; more answers.  Every racer is a complete search, so a racer that contributed
  ;; something the others missed would be a bug in the others.
  (tu/with-terms [edgeOf anc reach mid1 mid2 PortContext]
    (tu/with-terms [PtA PtB PtC]
      (branching-kb! kb edgeOf anc reach mid1 mid2 PortContext [PtA PtB PtC])
      (let [goals [(list reach '?x '?z)]
            union (set (inf/portfolio-solutions kb goals PortContext {:max-depth 4}))
            before (tu/content-count kb)]
        (is (seq union))
        (doseq [t inf/default-racers]
          (is (= union (answers kb goals PortContext t 4))
              (str "racer " t " does not agree with the union")))
        (testing "racing readers writes nothing"
          (is (= before (tu/content-count kb))))
        (testing "and an incomplete racer is refused rather than raced"
          (is (= :incomplete-racer
                 (:type (try (inf/portfolio-solutions kb goals PortContext
                                                      {:strategy {:first-result? true}})
                             (catch clojure.lang.ExceptionInfo e (ex-data e)))))))
        (testing "solutions routes to it on request"
          (is (= union (set (inf/solutions kb goals PortContext
                                           {:portfolio? true :max-depth 4})))))))))

;; ---- choosing one without a caller ---------------------------------------

(tu/deftest-kb auto-strategy-reads-the-shape-of-the-query
  (tu/with-terms [edgeOf anc reach mid1 mid2 AutoContext]
    (tu/with-terms [AuA AuB AuC]
      (branching-kb! kb edgeOf anc reach mid1 mid2 AutoContext [AuA AuB AuC])
      (let [pick #(tac/auto-strategy kb %1 AutoContext %2)]
        (is (= :cost (pick [(list reach '?x '?z)] 0))
            "with no rewriting allowance the root is the whole search")
        (is (= :portfolio (pick [(list anc '?x '?y) (list anc '?y '?z)] 4))
            "a conjunction has more than one plausible route")
        (is (= :portfolio (pick [(list reach '?x '?z)] 4))
            "two rules conclude reach")
        (is (= :depth-first (pick [(list mid1 '?x '?z)] 4))
            "one rule concludes mid1 — nothing to hedge")
        (is (= :depth-first (pick [(list edgeOf '?x '?z)] 4))
            "no rule concludes edgeOf either"))
      (testing "and an explicit strategy turns the probe off"
        (let [goals [(list reach '?x '?z)]]
          (is (= (answers kb goals AutoContext :cost 4)
                 (set (inf/solutions kb goals AutoContext
                                     {:auto? true :strategy :cost :max-depth 4}))
                 (set (inf/solutions kb goals AutoContext
                                     {:auto? true :max-depth 4})))))))))

;; ---- the seam ------------------------------------------------------------

(tu/deftest-kb the-strategy-reaches-the-engine-through-a-dynamic-var-too
  (tu/with-terms [edgeOf anc reach mid1 mid2 SeamContext]
    (tu/with-terms [SmA SmB SmC]
      (branching-kb! kb edgeOf anc reach mid1 mid2 SeamContext [SmA SmB SmC])
      (let [goals [(list reach '?x '?z)]]
        (is (= :ground-first (:tactician (:strategy (inf/session kb goals SeamContext {:max-depth 4})))))
        (binding [inf/*strategy* :breadth-first]
          (is (= :breadth-first (:tactician (:strategy (inf/session kb goals SeamContext {:max-depth 4})))))
          (is (= (answers kb goals SeamContext :cost 4)
                 (set (inf/solutions kb goals SeamContext {:max-depth 4})))
              "and it must not change what comes back"))))))

(tu/deftest-kb the-public-surface-carries-the-strategy-to-whichever-engine-runs
  (tu/with-terms [edgeOf anc reach mid1 mid2 OptContext]
    (tu/with-terms [OpA OpB OpC]
      (branching-kb! kb edgeOf anc reach mid1 mid2 OptContext [OpA OpB OpC])
      (let [goal (list reach '?x '?z)]
        (binding [v/*query-engine* :inference, inf/*max-depth* 8]
          (let [baseline (set (v/prove kb goal OptContext))]
            (is (seq baseline))
            (doseq [opts [:depth-first
                          {:strategy :breadth-first}
                          {:portfolio? true}
                          {:auto? true}]]
              (binding [v/*query-options* opts]
                (is (= baseline (set (v/prove kb goal OptContext)))
                    (str opts " changed the answer set"))))
            (testing "and a bounded run takes the strategy without losing its tail"
              (binding [v/*query-options* :ground-first]
                (let [r (v/prove-within kb goal OptContext {:max-results 1})]
                  (is (= :capped (:status r)))
                  (is (= baseline (into (set (:results r))
                                        (:results (v/resume r {}))))))))))
        (testing "the DFS ignores it entirely"
          (binding [v/*query-engine* :dfs v/*query-options* {:portfolio? true}]
            (is (seq (v/prove kb goal OptContext)))))))))
