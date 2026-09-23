;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inference-test
  "The node engine's own contract (`vaelii.impl.inference`): the residual transformation,
  per-literal depth, binding flow, guards, the claimed-key set, the frontier's order,
  and the structure of the tree it leaves behind.

  Answer-set agreement with the DFS is the criterion that actually decides whether this
  engine is right, and it lives in the adjacent namespace in `inference_parity_test`.  What is here is the
  diagnosis when that one goes red."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inf]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- answers
  "Every solution the node engine finds for `goals` in `context`, as a set."
  ([kb goals context] (answers kb goals context 8))
  ([kb goals context depth]
   (set (inf/solutions kb goals context {:max-depth depth}))))

(defn- values [sols var] (set (map #(get % var) sols)))

;; ---- shape ---------------------------------------------------------------

(tu/deftest-kb a-node-that-solves-against-facts-alone-is-a-completed-proof
  (tu/with-terms [parentOf CxShape]
    (tu/with-terms [ShapeA ShapeB]
      (v/assert kb (list parentOf ShapeA ShapeB) CxShape)
      (testing "depth 0 — no rewrite is possible, and the root still answers"
        (is (= #{{'?y ShapeB}} (answers kb [(list parentOf ShapeA '?y)] CxShape 0))))
      (testing "a ground goal that holds proves once, with an empty binding"
        (is (= #{{}} (answers kb [(list parentOf ShapeA ShapeB)] CxShape))))
      (testing "a goal nothing answers drains the frontier and returns nothing"
        (let [sess (inf/session kb [(list parentOf ShapeB '?y)] CxShape {:max-depth 2})]
          (is (empty? (doall (inf/search-seq sess))))
          (is (zero? (:frontier (inf/tree-stats sess))) "the queue was not drained")
          (is (zero? (:solutions (inf/tree-stats sess)))))))))

(tu/deftest-kb a-rule-is-rewritten-into-its-antecedents
  (tu/with-terms [parentOf anc CxShape]
    (tu/with-terms [RwA RwB]
      (v/assert kb (list parentOf RwA RwB) CxShape)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxShape
                     {:direction :backward})
      (testing "one rewrite reaches it, none does not"
        (is (= #{RwB} (values (answers kb [(list anc RwA '?z)] CxShape 1) '?z)))
        (is (empty? (answers kb [(list anc RwA '?z)] CxShape 0)))))))

;; ---- residuals and per-literal depth -------------------------------------

(defn- chain-of-rules!
  "`(p0 ?x)` concluded from `(p1 ?x)` concluded from … from a stored `(base Ind)`, so
  proving `(p0 Ind)` takes exactly `n` rewrites."
  [kb base ind pred n context]
  (v/assert kb (list base ind) context)
  (doseq [i (range n)]
    (v/assert-rule kb [(list (symbol (str pred (inc i))) '?x)]
                   (list (symbol (str pred i)) '?x) context {:direction :backward}))
  (v/assert-rule kb [(list base '?x)] (list (symbol (str pred n)) '?x) context
                 {:direction :backward}))

(tu/deftest-kb depth-bounds-the-rewrites-a-literal-may-take
  (tu/with-terms [base CxDepth]
    (tu/with-terms [DepthInd]
      (chain-of-rules! kb base DepthInd "tmp_depth_p" 2 CxDepth)
      (let [goal (list 'tmp_depth_p0 DepthInd)]
        (is (empty? (answers kb [goal] CxDepth 2)) "3 rewrites are needed")
        (is (= #{{}} (answers kb [goal] CxDepth 3)))
        (is (= #{{}} (answers kb [goal] CxDepth 5)) "a larger bound finds the same")))))

(tu/deftest-kb each-conjunct-carries-its-own-depth
  ;; The DFS gives a conjunction one budget for all of it, so whichever literal is
  ;; expanded first can spend the lot.  A node gives each conjunct its own, decremented
  ;; only for the one actually rewritten — so a cheap conjunct beside an expensive one
  ;; does not have to pay for it.
  (tu/with-terms [base CxPerLit]
    (tu/with-terms [PerLitInd]
      (chain-of-rules! kb base PerLitInd "tmp_shallow" 0 CxPerLit)   ; 1 rewrite
      (chain-of-rules! kb base PerLitInd "tmp_deeper" 2 CxPerLit)    ; 3 rewrites
      (let [conj-goal [(list 'tmp_shallow0 PerLitInd) (list 'tmp_deeper0 PerLitInd)]]
        (is (empty? (answers kb conj-goal CxPerLit 2)))
        (is (= #{{}} (answers kb conj-goal CxPerLit 3))
            "3 is what the deeper conjunct needs; the shallow one must not have spent it")))))

(tu/deftest-kb two-copies-of-one-sentence-keep-independent-counters
  (tu/with-terms [base CxDup]
    (tu/with-terms [DupInd]
      (chain-of-rules! kb base DupInd "tmp_dup" 1 CxDup)       ; 2 rewrites each
      (let [g (list 'tmp_dup0 DupInd)]
        (is (empty? (answers kb [g g] CxDup 1)))
        (is (= #{{}} (answers kb [g g] CxDup 2))
            "the first copy's rewrites must not be charged to the second")))))

(tu/deftest-kb a-multi-antecedent-rule-gives-every-conjunct-the-same-remaining-depth
  (tu/with-terms [leftOf rightOf between CxBetween]
    (tu/with-terms [BwA BwB BwC]
      (v/assert kb (list leftOf BwA BwB) CxBetween)
      (v/assert kb (list rightOf BwC BwB) CxBetween)
      (v/assert-rule kb [(list leftOf '?a '?b) (list rightOf '?c '?b)]
                     (list between '?a '?b '?c) CxBetween {:direction :backward})
      (is (= #{{'?a BwA '?b BwB '?c BwC}}
             (answers kb [(list between '?a '?b '?c)] CxBetween 1))))))

;; ---- binding flow --------------------------------------------------------

(tu/deftest-kb a-rewrite-carries-bindings-into-and-out-of-the-query-variables
  (tu/with-terms [edgeOf hop CxBind]
    (tu/with-terms [BnP BnQ BnR]
      (v/assert kb (list edgeOf BnP BnQ) CxBind)
      (v/assert kb (list edgeOf BnQ BnR) CxBind)
      (v/assert-rule kb [(list edgeOf '?x '?y)] (list hop '?x '?y) CxBind
                     {:direction :backward})
      (testing "the first argument bound, the second open"
        (is (= #{BnQ} (values (answers kb [(list hop BnP '?y)] CxBind) '?y))))
      (testing "the second bound, the first open"
        (is (= #{BnP} (values (answers kb [(list hop '?x BnQ)] CxBind) '?x))))
      (testing "both open"
        (is (= #{{'?x BnP '?y BnQ} {'?x BnQ '?y BnR}}
               (answers kb [(list hop '?x '?y)] CxBind))))
      (testing "both ground and disagreeing"
        (is (empty? (answers kb [(list hop BnP BnR)] CxBind))))
      (testing "a conjunctive query joins on the shared variable"
        (is (= #{{'?x BnP '?y BnQ '?z BnR}}
               (answers kb [(list hop '?x '?y) (list hop '?y '?z)] CxBind)))))))

(tu/deftest-kb two-rules-concluding-one-goal-both-answer-it
  (tu/with-terms [byLand bySea reachable CxMulti]
    (tu/with-terms [MtA MtB]
      (v/assert kb (list byLand MtA) CxMulti)
      (v/assert kb (list bySea MtB) CxMulti)
      (v/assert-rule kb [(list byLand '?x)] (list reachable '?x) CxMulti
                     {:direction :backward})
      (v/assert-rule kb [(list bySea '?x)] (list reachable '?x) CxMulti
                     {:direction :backward})
      (is (= #{MtA MtB} (values (answers kb [(list reachable '?x)] CxMulti) '?x))))))

;; ---- joins and the diamond -----------------------------------------------

(tu/deftest-kb a-diamond-answers-once-and-claims-the-shared-node-once
  ;; Two rules concluding `top` whose antecedents converge on one `base` literal.  The
  ;; two routes reach the same residual, and the second arrival is dropped before it is
  ;; enqueued rather than expanded again.
  (tu/with-terms [base mid1 mid2 top CxDia]
    (tu/with-terms [DiaX]
      (v/assert kb (list base DiaX) CxDia)
      (v/assert-rule kb [(list base '?x)] (list mid1 '?x) CxDia {:direction :backward})
      (v/assert-rule kb [(list base '?x)] (list mid2 '?x) CxDia {:direction :backward})
      (v/assert-rule kb [(list mid1 '?x)] (list top '?x) CxDia {:direction :backward})
      (v/assert-rule kb [(list mid2 '?x)] (list top '?x) CxDia {:direction :backward})
      (let [sess (inf/session kb [(list top '?x)] CxDia {:max-depth 3})
            sols (set (doall (inf/search-seq sess)))
            st   (inf/tree-stats sess)]
        (is (= #{{'?x DiaX}} sols) "one answer, not two")
        (is (pos? (:dropped st)) "the converging arrival was never dropped")
        (is (= (:nodes st) (:expanded st)) "a claimed node must be expanded exactly once")))))

(tu/deftest-kb a-four-literal-conjunction-joins-across-all-of-them
  (tu/with-terms [pA pB pC pD CxJoin]
    (tu/with-terms [JnOne JnTwo]
      (doseq [[p i] [[pA JnOne] [pB JnOne] [pC JnOne] [pD JnOne]
                     [pA JnTwo] [pB JnTwo] [pC JnTwo]]]
        (v/assert kb (list p i) CxJoin))
      (is (= #{JnOne}
             (values (answers kb [(list pA '?x) (list pB '?x) (list pC '?x) (list pD '?x)]
                              CxJoin)
                     '?x))))))

;; ---- guards --------------------------------------------------------------

(tu/deftest-kb an-exception-is-asked-at-the-nodes-own-solve
  ;; A node has no rule frame to check a guard in, and needs none: its inline solve is
  ;; the moment the argument is complete.
  (tu/with-terms [wings flies odd CxGuard]
    (tu/with-terms [GdBird GdPenguin]
      (v/assert kb (list wings GdBird) CxGuard)
      (v/assert kb (list wings GdPenguin) CxGuard)
      (v/assert kb (list odd GdPenguin) CxGuard)
      (v/assert kb (list 'exceptWhen (list odd '?x)
                         (list 'set/defaultRule
                               (list 'implies (list wings '?x) (list flies '?x))))
                CxGuard)
      (testing "a variable exception blocks exactly the bindings it holds of"
        (is (= #{GdBird} (values (answers kb [(list flies '?x)] CxGuard) '?x))))
      (testing "and the same asked of the excepted individual directly"
        (is (empty? (answers kb [(list flies GdPenguin)] CxGuard)))
        (is (= #{{}} (answers kb [(list flies GdBird)] CxGuard)))))))

;; ---- termination ---------------------------------------------------------

(tu/deftest-kb a-cyclic-rule-set-drains-the-frontier
  (tu/with-terms [pingOf pongOf CxCycle]
    (tu/with-terms [CycInd]
      (v/assert-rule kb [(list pongOf '?x)] (list pingOf '?x) CxCycle
                     {:direction :backward})
      (v/assert-rule kb [(list pingOf '?x)] (list pongOf '?x) CxCycle
                     {:direction :backward})
      (let [sess (inf/session kb [(list pingOf CycInd)] CxCycle {:max-depth 6})]
        (is (empty? (doall (inf/search-seq sess))) "nothing supports either predicate")
        (is (zero? (:frontier (inf/tree-stats sess))) "the search did not terminate")))))

(tu/deftest-kb a-repeated-conjunct-collapses-and-a-cycle-stops-growing-the-residual
  ;; The cycle runs through a rule with a multi-literal antecedent, which is what grows
  ;; a conjunction: a one-antecedent rule rewrites a literal into a literal and never
  ;; writes a second copy of a sentence the conjunction already holds.
  ;;
  ;;   (alpha ?x) ∧ (beta ?x) ⇒ (paired ?x)
  ;;   (paired ?x) ⇒ (alpha ?x)          (paired ?x) ⇒ (beta ?x)
  ;;
  ;; so (paired ?x) rewrites to (alpha ?x) ∧ (beta ?x), then to (paired ?x) ∧ (beta ?x),
  ;; then to (alpha ?x) ∧ (beta ?x) ∧ (beta ?x), whose third conjunct is the repeat.
  ;; Conjunction is idempotent, so the repeat collapses onto the copy already there and
  ;; the search returns to a conjunction it holds a key for.  Carrying every repeat
  ;; instead, this query expands 1,445 nodes at the bound below, and 15,130 at a bound
  ;; of 7.
  (tu/with-terms [alpha beta paired CxIdem]
    (tu/with-terms [IdemBoth IdemHalf]
      (v/assert kb (list alpha IdemBoth) CxIdem)
      (v/assert kb (list beta IdemBoth) CxIdem)
      (v/assert kb (list alpha IdemHalf) CxIdem)
      (v/assert-rule kb [(list alpha '?x) (list beta '?x)] (list paired '?x) CxIdem
                     {:direction :backward})
      (v/assert-rule kb [(list paired '?x)] (list alpha '?x) CxIdem {:direction :backward})
      (v/assert-rule kb [(list paired '?x)] (list beta '?x) CxIdem {:direction :backward})
      (let [sess (inf/session kb [(list paired '?x)] CxIdem {:max-depth 6})
            sols (set (doall (inf/search-seq sess)))
            st   (inf/tree-stats sess)]
        (is (= #{{'?x IdemBoth}} sols)
            "the individual holding one half of the rule's antecedent is not paired")
        (is (zero? (:frontier st)) "the search did not run to exhaustion")
        (is (< (:nodes st) 200)
            "the residual grew a conjunct per turn of the cycle")
        (testing "and no node carries one sentence twice"
          ;; counted rather than asserted node by node: a failure here is most of the
          ;; tree, and printing the tree buries the count that says how much of it
          (let [repeats (filter (fn [n] (let [ss (mapv :sentence (:literals n))]
                                          (not= (count ss) (count (set ss)))))
                                (vals @(:nodes sess)))]
            (is (zero? (count repeats)) "nodes carrying a repeated conjunct")))))))

;; ---- deferred literals ---------------------------------------------------

(tu/deftest-kb a-deferred-literal-is-computed-and-never-rewritten
  ;; `different` / `evaluate` / `unknown` are not stored facts and not rule heads.  A
  ;; node must route them through the registry and must not build residual children for
  ;; them, or a rule with such an antecedent silently proves nothing.
  (tu/with-terms [pairOf distinctPair CxDefer]
    (tu/with-terms [DfA DfB]
      (v/assert kb (list pairOf DfA DfB) CxDefer)
      (v/assert kb (list pairOf DfA DfA) CxDefer)
      (v/assert-rule kb [(list pairOf '?x '?y) (list 'different '?x '?y)]
                     (list distinctPair '?x '?y) CxDefer {:direction :backward})
      (is (= #{{'?x DfA '?y DfB}}
             (answers kb [(list distinctPair '?x '?y)] CxDefer))
          "the reflexive pair must be computed away, not matched"))))

;; ---- structure: the queue, the claim, the tree ---------------------------

(tu/deftest-kb the-frontier-pops-the-lowest-estimate-first
  (let [k  (fn [n] [[(list 'p n)] 0])
        q  (-> (inf/empty-queue) (inf/queue-push 90 (k 1) 1) (inf/queue-push 10 (k 2) 2)
               (inf/queue-push 50 (k 3) 3))]
    (is (nil? (inf/queue-pop (inf/empty-queue))) "an empty queue must pop nil")
    (let [[e1 q1] (inf/queue-pop q)
          [e2 q2] (inf/queue-pop q1)
          [e3 q3] (inf/queue-pop q2)]
      (is (= [[10 (k 2) 2] [50 (k 3) 3] [90 (k 1) 1]] [e1 e2 e3]))
      (is (nil? (inf/queue-pop q3))))))

(tu/deftest-kb a-cost-tie-on-the-frontier-breaks-on-content-and-not-on-the-id
  ;; The estimate is coarse and ties constantly, and the tie decides which node a
  ;; `:node-budget` run expands before it stops.  Breaking it on the id would key a
  ;; bounded search's answer set on the order the nodes were minted, which is the order
  ;; the rules were asserted in.
  (let [early [[(list 'zLater 'A)] 0]        ; minted first, content-greater
        late  [[(list 'aSooner 'A)] 0]       ; minted second, content-lesser
        q     (-> (inf/empty-queue) (inf/queue-push 7 early 1) (inf/queue-push 7 late 2))
        [[_ c _]] (inf/queue-pop q)]
    (is (= late c) "the content-lesser node pops first, though its id is the later one")
    (is (= 2 (count q)) "and neither is dropped — equal costs are still two entries")))

(tu/deftest-kb a-key-is-claimed-once-and-the-claim-is-what-stops-a-re-arrival
  (tu/with-terms [parentOf anc CxKey]
    (tu/with-terms [KyA KyB]
      (v/assert kb (list parentOf KyA KyB) CxKey)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxKey
                     {:direction :backward})
      (let [sess (inf/session kb [(list anc '?x '?z)] CxKey {:max-depth 2})
            root (get @(:nodes sess) 0)]
        (is (= 1 (count @(:claimed sess))) "the root claims its key when it is enqueued")
        (is (contains? @(:claimed sess) (inf/node-key root)))
        (testing "the root is the asker's question canonicalized, and keeps their names"
          (is (= [(list anc '?var0 '?var1)] (mapv :sentence (:literals root))))
          (is (= '{?x ?var0, ?z ?var1} (:answer-terms root))))
        (testing "two alpha-variant questions are one conjunction — that is what canonical buys"
          (let [other (inf/session kb [(list anc '?who '?whom)] CxKey {:max-depth 2})]
            (is (= (mapv :sentence (:literals root))
                   (mapv :sentence (:literals (get @(:nodes other) 0)))))))
        (testing "a constant reaching a literal changes the key, because it changes the question"
          (is (not= (inf/node-key root)
                    (inf/node-key (assoc root :literals [{:sentence (list anc KyA '?var1)
                                                          :depth 2}])))))
        (testing "and one conjunction asked on behalf of a different answer is a different node"
          ;; same literals, opposite projection: collapsing these loses an answer set
          (is (not= (inf/node-key root)
                    (inf/node-key (assoc root :answer-terms '{?x ?var1, ?z ?var0})))))))))

(tu/deftest-kb the-search-tree-outlives-the-search
  (tu/with-terms [parentOf anc CxTree]
    (tu/with-terms [TrA TrB]
      (v/assert kb (list parentOf TrA TrB) CxTree)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxTree
                     {:direction :backward})
      (let [sess (inf/session kb [(list anc '?x '?z)] CxTree {:max-depth 2})
            sols (doall (inf/search-seq sess))
            st   (inf/tree-stats sess)]
        (is (seq sols))
        (is (>= (:nodes st) 2) "root plus at least one child")
        (is (= (:nodes st) (:expanded st)))
        (is (pos? (:max-depth st)) "no rewrite was recorded")
        (testing "every node still names the one it came from"
          (let [ns (vals @(:nodes sess))]
            (is (= 1 (count (filter #(nil? (:parent-id %)) ns))) "exactly one root")
            (is (every? #(contains? @(:nodes sess) (:parent-id %))
                        (remove #(nil? (:parent-id %)) ns)))))
        (testing "and carries the rules that licensed it"
          (is (some #(seq (:supports %)) (vals @(:nodes sess)))))))))

;; ---- purity --------------------------------------------------------------

(tu/deftest-kb a-query-leaves-the-kb-exactly-as-it-found-it
  ;; An engine that materializes its conclusions is a forward chainer in disguise.
  (tu/with-terms [parentOf anc CxPure]
    (tu/with-terms [PrA PrB PrC]
      (v/assert kb (list parentOf PrA PrB) CxPure)
      (v/assert kb (list parentOf PrB PrC) CxPure)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxPure
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     CxPure {:direction :backward})
      (let [before (tu/content-count kb)]
        (is (seq (answers kb [(list anc '?x '?z)] CxPure)))
        (is (= before (tu/content-count kb))
            "the search created sentexes or justifications")))))

;; ---- laziness ------------------------------------------------------------

(tu/deftest-kb the-result-stream-expands-a-node-per-pull
  (tu/with-terms [wideOf CxWide]
    (let [inds (mapv #(symbol (str "TmpWide" % "Node")) (range 6))]
      (doseq [i inds] (v/assert kb (list wideOf i) CxWide))
      (let [sess (inf/session kb [(list wideOf '?x)] CxWide {:max-depth 2})
            two  (doall (take 2 (inf/search-seq sess)))]
        (is (= 2 (count two)))
        (is (<= (:expanded (inf/tree-stats sess)) 2)
            "a bounded consumer must not have driven the whole search"))
      (testing "and reading it dry returns everything"
        (is (= (set inds)
               (values (answers kb [(list wideOf '?x)] CxWide) '?x)))))))

(defn- wide-unproductive!
  "`target` concluded by `n` backward rules whose antecedents nothing stores — a frontier
  of `n` children each expanding to nothing — plus one route that answers: `(have A)`."
  [kb target have A ctx n]
  (v/with-deferred-settle kb
    (doseq [i (range n)]
      (v/assert-rule kb [(list (tu/tmp-pred (str "unprod" i)) '?x)] (list target '?x) ctx
                     {:direction :backward}))
    (v/assert-rule kb [(list have '?x)] (list target '?x) ctx {:direction :backward})
    (v/assert kb (list have A) ctx)))

(tu/deftest-kb a-deadline-stops-the-drive-at-the-next-node-not-the-next-answer
  ;; `search-seq` pulls one element by stepping until a node yields, so a deadline held
  ;; between its elements is held only after a whole unproductive stretch — here the
  ;; root's expansion builds the whole frontier, and every child but one expands to
  ;; nothing.  `search-within` checks the bounds before every expansion, so a deadline
  ;; that passes inside the stretch stops the drive at the next node; the session it
  ;; leaves behind is the continuation.  Two milliseconds is well under what the stretch
  ;; costs and well over one expansion, so the count below is a shape, not a timing.
  (tu/with-terms [target have HaveA CxDl]
    (let [width 160]
      (wide-unproductive! kb target have HaveA CxDl width)
      (let [goals [(list target '?x)]
            sess  (inf/session kb goals CxDl {:max-depth 3})
            r     (inf/search-within sess {:max-ms 2})]
        (is (= :timeout (:status r)))
        (is (< (:expanded (inf/tree-stats sess)) width)
            "the deadline must stop the drive inside the unproductive frontier, not after it")
        (is (< (:elapsed-ms r) 5000) "and the step returns near its bound, not near the run's")
        (is (fn? (:resume r)))
        (testing "resuming the same session under a generous budget finishes the search"
          (let [r2 ((:resume r) {:max-ms 60000})]
            (is (= :complete (:status r2)))
            (is (= #{HaveA} (values (into (set (:results r)) (:results r2)) '?x)))
            (is (nil? (:resume r2)))))
        (testing "the public entry point holds the same line under the node engine"
          (binding [v/*query-engine* :inference, inf/*max-depth* 3]
            (let [r  (v/prove-within kb (list target '?x) CxDl {:max-ms 2 :max-depth 3})
                  r2 (v/resume r {:max-ms 60000})]
              (is (= :timeout (:status r)))
              (is (< (:elapsed-ms r) 5000))
              (is (= :complete (:status r2)))
              (is (= #{HaveA} (values (into (set (:results r)) (:results r2)) '?x))))))))))

(tu/deftest-kb a-result-cap-returns-exactly-n-and-carries-the-rest
  ;; One expansion can complete several solutions at once; a cap of n returns n and the
  ;; remainder heads the continuation rather than being dropped or over-delivered.
  (tu/with-terms [wideOf CxCap]
    (let [inds (mapv #(symbol (str "TmpCap" % "Node")) (range 5))]
      (doseq [i inds] (v/assert kb (list wideOf i) CxCap))
      (let [sess (inf/session kb [(list wideOf '?x)] CxCap {:max-depth 2})
            r1   (inf/search-within sess {:max-results 2})]
        (is (= :capped (:status r1)))
        (is (= 2 (:count r1)))
        (loop [r r1, acc (vec (:results r1))]
          (if (:resume r)
            (let [r' ((:resume r) {:max-results 2})
                  acc (into acc (:results r'))]
              (is (<= (:count r') 2))
              (recur r' acc))
            (do (is (= :complete (:status r)))
                (is (= (set inds) (values (set acc) '?x)))
                (is (= 5 (count acc)) "each answer once across the steps"))))))))

;; ---- the selector --------------------------------------------------------

(tu/deftest-kb the-selector-routes-and-defaults-to-the-dfs
  (tu/with-terms [parentOf anc CxSel]
    (tu/with-terms [SlA SlB]
      (v/assert kb (list parentOf SlA SlB) CxSel)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxSel
                     {:direction :backward})
      (is (= (or (tu/query-engine-override) :dfs) v/*query-engine*)
          "the default must stay :dfs; under the sweep the engine is the one it set")
      (let [goal (list anc SlA '?z)]
        (testing ":inference answers what :dfs answers"
          (is (= #{SlB} (values (set (v/prove kb goal CxSel)) '?z)))
          (is (= #{SlB} (values (binding [v/*query-engine* :inference, inf/*max-depth* 8]
                                  (set (v/prove kb goal CxSel)))
                                '?z))))
        (testing ":hybrid sends a depth-0 budget to the DFS and anything deeper to the node engine"
          (binding [v/*query-engine* :hybrid]
            (is (= :complete (:status (v/prove-within kb goal CxSel {:max-depth 0}))))
            (let [r (v/prove-within kb goal CxSel {:max-depth 3})]
              (is (= :complete (:status r)))
              (is (= #{SlB} (values (set (:results r)) '?z))))))
        (testing "a bounded run is a prefix, and resume continues it"
          (binding [v/*query-engine* :inference, inf/*max-depth* 8]
            (let [r (v/prove-within kb goal CxSel {:max-results 0})]
              (is (= :capped (:status r)))
              (is (= #{SlB} (values (set (:results (v/resume r {}))) '?z))))))))))

;; ---- the proof tree ------------------------------------------------------
;; `query` with `{:proof? true}` returns the derivation the search took, replayed out of
;; the node registry.  What is checked here is that it is a *faithful* replay: the rules
;; it names are the rules that fired, its leaves are literals the search really did hand
;; to the leaf solver, and one variable name means one thing across the whole tree —
;; which is the property a per-node namespace makes non-obvious.

(defn- rules-in
  "Every rule handle a proof tree names, depth-first.  A leaf names none."
  [tree]
  (mapcat (fn [n] (when (= :rule (:via n)) (cons (:rule n) (rules-in (:because n)))))
          tree))

(defn- leaves-in [tree]
  (mapcat (fn [n] (if (= :leaf (:via n)) [(:goal n)] (leaves-in (:because n)))) tree))

(tu/deftest-kb a-proof-names-the-rule-that-fired-and-the-literals-under-it
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann CxPf]
    (v/assert kb (list parentOf Tom Bob) CxPf)
    (v/assert kb (list parentOf Bob Ann) CxPf)
    (let [rh (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                            (list grandparentOf '?x '?z) CxPf
                            {:direction :backward})
          [r & more] (v/query kb (list grandparentOf Tom '?w) CxPf
                              {:max-depth 2 :proof? true})]
      (testing "one answer, and it comes back with its bindings beside its proof"
        (is (empty? more))
        (is (= {'?w Ann} (:bindings r)))
        (is (vector? (:proof r)) "one tree per conjunct of the query"))
      (let [[top] (:proof r)]
        (testing "the root of the tree is the query's own conjunct, derived by the rule"
          (is (= :rule (:via top)))
          (is (= rh (:rule top)) "the handle of the rule that actually fired")
          (is (= grandparentOf (first (:goal top)))))
        (testing "and the rule reads as its author wrote it, not in canonical variables"
          (is (= (list 'implies
                       (list 'and (list parentOf '?x '?y) (list parentOf '?y '?z))
                       (list grandparentOf '?x '?z))
                 (:sentence top))))
        (testing "its children are the antecedents, and nothing below them was rewritten"
          (is (= 2 (count (:because top))))
          (is (every? #(= :leaf (:via %)) (:because top)))
          (is (every? #(= parentOf (first (:goal %))) (:because top))))))))

(tu/deftest-kb one-variable-name-means-one-thing-across-a-nested-proof
  ;; Each node canonicalizes to `?var0 ?var1 …` in a namespace of its own, so a tree
  ;; assembled straight from the nodes would use `?var0` for a different variable at
  ;; every level.  The replay pushes each level forward into the next node's numbering,
  ;; which is what makes the finished tree readable as one derivation.
  (tu/with-terms [parentOf anc Tom Bob Ann Zed CxPf]
    (doseq [[a b] [[Tom Bob] [Bob Ann] [Ann Zed]]]
      (v/assert kb (list parentOf a b) CxPf))
    (let [base (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxPf
                              {:direction :backward})
          step (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)]
                              (list anc '?x '?z) CxPf {:direction :backward})
          by-answer (into {} (map (juxt (comp '?w :bindings) :proof))
                          (v/query kb (list anc Tom '?w) CxPf
                                   {:max-depth 4 :proof? true}))]
      (testing "every reachable ancestor is answered, each with a proof"
        (is (= #{Bob Ann Zed} (set (keys by-answer)))))
      (testing "the one-hop answer uses the base rule alone"
        (is (= [base] (rules-in (by-answer Bob)))))
      (testing "the three-hop answer stacks the recursive rule twice over the base"
        (is (= [step step base] (rules-in (by-answer Zed)))))
      (testing "and its leaves chain end to end — the join variables line up"
        ;; (parentOf Tom ?a) (parentOf ?a ?b) (parentOf ?b ?c), one namespace throughout
        (let [ls (vec (leaves-in (by-answer Zed)))]
          (is (= 3 (count ls)))
          (is (= Tom (second (first ls))))
          (is (= (nth (nth ls 0) 2) (second (nth ls 1))) "first hop feeds the second")
          (is (= (nth (nth ls 1) 2) (second (nth ls 2))) "second feeds the third"))))))

(tu/deftest-kb without-the-option-nothing-changes-shape
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann CxPf]
    (v/assert kb (list parentOf Tom Bob) CxPf)
    (v/assert kb (list parentOf Bob Ann) CxPf)
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) CxPf {:direction :backward})
    (let [goal (list grandparentOf Tom '?w)]
      (testing "the default result is binding maps, with no proof key anywhere"
        (is (= [{'?w Ann}] (vec (v/query kb goal CxPf {:max-depth 2})))))
      (testing "and asking for proofs does not change which answers come back"
        (is (= (set (v/query kb goal CxPf {:max-depth 2}))
               (set (map :bindings (v/query kb goal CxPf
                                            {:max-depth 2 :proof? true}))))))
      (testing "`query?` ignores it rather than testing a map for emptiness"
        (is (v/query? kb goal CxPf {:max-depth 2 :proof? true}))))))

;;; ── the depth bound is required, not defaulted ────────────────────────

(tu/deftest-kb the-node-engine-refuses-to-start-without-a-depth-bound
  ;; The bound is the termination condition rather than a tuning knob: a residual grows a
  ;; conjunct per rewrite, so the claimed-key set cannot stop a search that has no bound.
  ;; A default would be a number picked without looking at the data it bounds, and wrong
  ;; in the direction that loses answers — so the caller says, or the search does not
  ;; start.  Either of the two ways of saying it will do, and both are checked here.
  (let [goal (list 'genl '?x 'thing)]
    (binding [inf/*max-depth* nil]
      (let [d (try (inf/session kb [goal] 'CxUniverse)
                   nil
                   (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= :no-depth-bound (:type d))
            "neither option nor binding is a refusal, not a search on some default"))
      (testing "the option is one way to say it"
        (is (some? (inf/session kb [goal] 'CxUniverse {:max-depth 3})))))
    (testing "and the binding is the other"
      (binding [inf/*max-depth* 3]
        (is (some? (inf/session kb [goal] 'CxUniverse)))))))

