;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.chaining-contracts-test
  "The bounds on a forward-chaining run: the term-nesting bound, `:max-depth`,
  `:max-derivations`, `:max-ms` and `:stop?`, the `new?` check on the transitive re-seed,
  and the accepted option keys.  docs/inference.md, \"Forward chaining\"."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

;; ---- :max-derivations ---------------------------------------------------

(tu/deftest-kb default-chain-opts-bound-term-nesting-alone
  (is (= #{:max-term-depth} (set (keys v/default-chain-opts))))
  (is (pos-int? (:max-term-depth v/default-chain-opts))))

;; ---- the term-nesting bound -----------------------------------------------

(tu/deftest-kb a-function-free-chain-derives-every-link-with-no-options
  ;; One recursive rule over a 400-link line: the n-th conclusion is at derivation depth
  ;; n, and no bound applies to a rule set that builds no term.
  (tu/with-terms [linkA reach_a]
    (let [nodes (vec (repeatedly 401 #(tu/tmp-ind "Node")))]
      (v/assert kb (fwd [(list linkA '?x '?y) (list reach_a '?y)] (list reach_a '?x))
                'CxUniverse {:chain? false})
      (doseq [[a b] (partition 2 1 nodes)]
        (v/assert kb (list linkA a b) 'CxUniverse {:chain? false}))
      (v/assert kb (list reach_a (peek nodes)) 'CxUniverse)
      (let [last-run (:last (v/chain-stats kb))]
        (is (= 401 (v/count-with-functor kb reach_a)))
        (is (not (:truncated? last-run)))
        (is (nil? (:term-cut last-run)))))))

(tu/deftest-kb a-recursive-mint-ends-at-the-term-nesting-bound
  ;; `(num ?x) → (num (SuccFn ?x))` mints one constant per firing, and the n-th constant
  ;; nests n deep.  With `(result SuccFn num)` each mint stores `(num K)` as a premise at
  ;; derivation depth 0; the bound reads nesting, so it ends both at the same count.
  (doseq [result? [false true]]
    (tu/with-terms [SuccFn num]
      (v/assert kb (list 'reifiable_function SuccFn) 'CxUniverse)
      (when result? (v/assert kb (list 'result SuccFn num) 'CxUniverse))
      (v/assert kb (fwd [(list num '?x)] (list num (list SuccFn '?x))) 'CxUniverse)
      (v/assert kb (list num (tu/tmp-ind "Zero")) 'CxUniverse)
      (let [bound    (:max-term-depth v/default-chain-opts)
            last-run (:last (v/chain-stats kb))]
        (testing (str "result declared: " result?)
          (is (= (inc bound) (v/count-with-functor kb num)) "Zero and one constant per level")
          (is (not (:truncated? last-run)))
          (is (pos? (:term-cut last-run 0)))
          (testing "and a larger bound in a later forward-chain places what the default cut"
            (v/forward-chain kb {:max-term-depth (+ bound 2)})
            (is (= (+ bound 3) (v/count-with-functor kb num)))))))))

(tu/deftest-kb a-recursive-head-existential-ends-at-the-term-nesting-bound
  ;; Each witness is `(SkolemFn … ?x)` over the person it rests on, one level deeper.
  (tu/with-terms [person motherOf Tom]
    (v/assert kb (fwd [(list person '?x)]
                      (list 'exists '?m (list 'and (list motherOf '?m '?x) (list person '?m))))
              'CxUniverse)
    (v/assert kb (list person Tom) 'CxUniverse)
    (let [bound (:max-term-depth v/default-chain-opts)]
      (is (= (inc bound) (v/count-with-functor kb person)))
      (is (= bound (v/count-with-functor kb motherOf)))
      (is (pos? (:term-cut (:last (v/chain-stats kb)) 0))))))

(tu/deftest-kb a-rule-passing-a-term-deeper-than-the-bound-through-still-fires
  ;; `paired` builds `(SuccFn ?y)` beside the deep term it passes through, so the firing
  ;; is measured, and its conclusion nests no deeper than the fact it rests on.
  (tu/with-terms [SuccFn holds tag copied paired T]
    (let [deep (nth (iterate #(list SuccFn %) (tu/tmp-ind "Zero"))
                    (+ 4 (:max-term-depth v/default-chain-opts)))]
      (v/assert kb (list 'unreifiable_function SuccFn) 'CxUniverse)
      (v/assert kb (fwd [(list holds '?x)] (list copied '?x)) 'CxUniverse)
      (v/assert kb (fwd [(list holds '?x) (list tag '?y)] (list paired '?x (list SuccFn '?y)))
                'CxUniverse)
      (v/assert kb (list tag T) 'CxUniverse)
      (v/assert kb (list holds deep) 'CxUniverse)
      (is (= 1 (v/count-with-functor kb copied)))
      (is (= 1 (v/count-with-functor kb paired)))
      (is (nil? (:term-cut (:last (v/chain-stats kb))))))))

(tu/deftest-kb a-cycle-through-two-formulas-measures-the-same-from-either-constant
  ;; Two constants whose formulas name each other, as two merged formulas can.  The
  ;; measure ends, and a constant's nesting does not depend on which one a memo met first.
  (let [ka 'nat/TmpCycleA, kb2 'nat/TmpCycleB
        forms {ka (list 'TmpF kb2) kb2 (list 'TmpG (list 'TmpH ka))}
        nesting #'chain/term-nesting]
    (with-redefs [nat/nat-expression (fn [_ k] (forms k))]
      (let [fresh  #(java.util.HashMap.)
            a      (nesting kb (fresh) ka)
            b      (nesting kb (fresh) kb2)
            shared (fresh)]
        (is (= [4 4] [a b]))
        (is (= [b a] [(nesting kb shared kb2) (nesting kb shared ka)]))))))

(tu/deftest-kb an-unbounded-run-is-not-flagged-truncated
  (tu/with-terms [thing marked A B C D E F]
    (v/assert kb (fwd [(list thing '?x)] (list marked '?x)) 'CxNaturalWorld)
    (doseq [i [A B C D E F]]
      (v/assert kb (list thing i) 'CxNaturalWorld {:chain? false}))
    (let [{:keys [derived truncated?]} (v/forward-chain kb {})]
      (is (>= derived 6) "one conclusion per fact")
      (is (not truncated?)))))

(tu/deftest-kb max-derivations-bounds-a-run-that-depth-alone-would-not
  ;; A transitive closure over a line graph: every `path` fact beyond the direct
  ;; edges is derived, and the full closure is far larger than the bound.  Depth
  ;; alone would not stop it at 2 derivations.
  ;;
  ;; The bound is checked *between* agenda datums, not inside one firing, so a single
  ;; datum's fan-out can overshoot it — `:max-derivations` is a backstop against a
  ;; runaway run, not a precise quota.  Asserting well below the unbounded total is
  ;; what tests it without over-claiming.
  (tu/with-terms [edge path A B C D E CxGraph]
    (v/assert kb (list 'genlCx CxGraph 'CxUniverse) 'CxUniverse)
    (v/assert kb (fwd [(list edge '?x '?y)] (list path '?x '?y)) CxGraph)
    (v/assert kb (fwd [(list edge '?x '?y) (list path '?y '?z)]
                      (list path '?x '?z)) CxGraph)
    (doseq [[a b] [[A B] [B C] [C D] [D E]]]
      (v/assert kb (list edge a b) CxGraph {:chain? false}))
    (let [{:keys [derived truncated? bound]} (v/forward-chain kb {:max-derivations 2 :on-stop :keep})]
      (is truncated? "the run hit the derivation backstop")
      (is (= :max-derivations bound))
      (is (< derived 10)
          "the full closure over a 4-edge line is 10 paths; the bound stopped it short"))))

(tu/deftest-kb max-depth-still-bounds-a-deepening-chain
  ;; The other disjunct, for contrast: depth grows, so the depth bound fires.
  (tu/with-terms [edge path A B C D CxGraph]
    (v/assert kb (list 'genlCx CxGraph 'CxUniverse) 'CxUniverse)
    (v/assert kb (fwd [(list edge '?x '?y)] (list path '?x '?y)) CxGraph)
    (v/assert kb (fwd [(list edge '?x '?y) (list path '?y '?z)]
                      (list path '?x '?z)) CxGraph)
    (doseq [[a b] [[A B] [B C] [C D]]]
      (v/assert kb (list edge a b) CxGraph {:chain? false}))
    (let [{:keys [truncated?]} (v/forward-chain kb {:max-depth 1})]
      (is truncated? "a depth-1 bound cannot reach the two-hop path"))))

(tu/deftest-kb a-recursive-rule-concluding-a-transitive-predicate-converges
  ;; The `new?` check on `special/transitive-seeds` in `place-fact-conclusion`, and the
  ;; only thing that exercises it.
  ;;
  ;; A declared-transitive predicate's closure is answered rather than stored, so a
  ;; rule joined to one is re-driven by seeding the PARTNER antecedent's facts when a
  ;; link arrives.  When the rule *concludes* that same predicate, those partner facts
  ;; are the very ones whose firing concluded the link — so a re-derivation that
  ;; re-seeded them would re-drive its own trigger, and the agenda in `chain` is a
  ;; plain queue with no dedup.  Two `edge` facts are then enough to run to
  ;; `:max-derivations`: the run truncates, warns, and returns a fixpoint it never
  ;; reached, on a KB whose whole content is three derivable pairs.
  ;;
  ;; Seeding only for a NEW conclusion is what closes it, and it adds no work: a
  ;; re-derivation adds a justification rather than a link, so the closure it would
  ;; re-drive the join over is the one the join already ran against.
  ;;
  ;; The bound is well below the backstop and far above the answer, so the assertion
  ;; is about convergence rather than about a count: without the `new?` check this reaches
  ;; 500 with the closure still unfinished, and with it the run stops at three.
  (tu/with-terms [edge anc A B C CxDescent]
    (v/assert kb (list 'genlCx CxDescent 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'transitive anc) CxDescent {:strength :monotonic :chain? false})
    (v/assert kb (fwd [(list edge '?x '?y)] (list anc '?x '?y)) CxDescent {:chain? false})
    (v/assert kb (fwd [(list edge '?x '?y) (list anc '?y '?z)]
                      (list anc '?x '?z)) CxDescent {:chain? false})
    (doseq [[a b] [[A B] [B C]]]
      (v/assert kb (list edge a b) CxDescent {:chain? false}))
    (let [{:keys [derived truncated?]} (v/forward-chain kb {:max-derivations 500})]
      (is (not truncated?)
          "a two-edge line under a recursive transitive rule is a fixpoint, not a runaway")
      (is (< derived 20)
          "three pairs and their supporting placements — not hundreds")
      (is (= 3 (count (v/sentexes-matching kb (list anc '?x '?y) CxDescent)))
          "the closure over a two-edge line is A-B, B-C and A-C"))))

;; ---- :on-progress -------------------------------------------------------
;;
;; The fixpoint is the one phase of a bulk load that can run for minutes, so it reports
;; where it is and takes a throw as an abort.  Reporting is paced by wall-clock, which a
;; test cannot wait out quickly — a run big enough to take seconds is a slow test, and one
;; small enough to be quick reports once.  So the interval itself is a knob
;; (`:progress-every-ms 0`, report at every opportunity) and the runs stay small: a line
;; graph's transitive closure is quadratic in its edges, so 40 of them is hundreds of
;; agenda datums for four asserts of setup.

(defn- line-graph!
  "A `path`-closure rule set over a line of `n` edges, asserted without chaining.  Returns
  `[edge path context]`."
  [kb n]
  (let [edge (tu/tmp-pred "edge"), path (tu/tmp-pred "path"), ctx (tu/tmp-ctx "Graph")
        nodes (vec (repeatedly (inc n) #(tu/tmp-ind "N")))]
    (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
    (v/assert kb (fwd [(list edge '?x '?y)] (list path '?x '?y)) ctx {:chain? false})
    (v/assert kb (fwd [(list edge '?x '?y) (list path '?y '?z)] (list path '?x '?z))
              ctx {:chain? false})
    (doseq [[a b] (partition 2 1 nodes)]
      (v/assert kb (list edge a b) ctx {:chain? false}))
    [edge path ctx]))

(tu/deftest-kb a-long-run-reports-where-it-has-got-to
  (line-graph! kb 40)
  (let [seen (atom [])
        {:keys [derived]} (v/forward-chain kb {:progress-every-ms 0
                                               :on-progress #(swap! seen conj %)})]
    (is (> (count @seen) 1)
        "a run of hundreds of datums reports more than once — a bar that never moves is
         the thing this exists to stop")
    (is (= (map :derived @seen) (sort (map :derived @seen)))
        "the derived count only ever grows")
    (is (every? #(and (nat-int? (:derived %)) (nat-int? (:pending %))) @seen))
    (is (= derived (:derived (last @seen)))
        "the last report agrees with what the run returns")
    (is (zero? (:pending (last @seen)))
        "a fixpoint ends with an empty agenda")))

(tu/deftest-kb a-throwing-progress-callback-aborts-the-run
  ;; How a loader cancels under `:on-stop :keep`: what had been derived stays, since
  ;; conclusions are placed as they are made, so the KB holds a prefix of the run, which
  ;; `unload!` then takes down.
  (let [[_ path _] (line-graph! kb 40)
        closure    (/ (* 40 41) 2)]                  ; every ordered pair along the line
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"stop here"
                          (v/forward-chain kb {:progress-every-ms 0 :on-stop :keep
                                               :on-progress (fn [_] (throw (ex-info "stop here" {})))})))
    (is (< (v/count-with-functor kb path) closure)
        "the abort landed before the closure was complete")
    (v/forward-chain kb {})
    (is (= closure (v/count-with-functor kb path))
        "and a run from what it had placed reaches the same fixpoint")))

;; ---- a bound on the call: :max-ms and :stop? -----------------------------
;;
;; A firing that mints a term runs the mint's assert, and the assert's seeds join the
;; run that minted it, so a run over a line of links mints one term per node in one run.

(defn- minting-line!
  "Over a line of `n` links, `(tagged (NextFn b))` from `(nextOf a k)` and `(link a b)`:
  the firing for each node mints `(NextFn b)`, whose mint asserts the projection
  `(nextOf b K)`, which the next firing joins.  Returns `[nextOf tagged]`."
  [kb n]
  (tu/with-terms [NextFn nextOf link tagged]
    (v/assert kb (list 'reifiable_function NextFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate NextFn nextOf 2) 'CxUniverse)
    (v/assert kb (fwd [(list nextOf '?a '?k) (list link '?a '?b)] (list tagged (list NextFn '?b)))
              'CxUniverse {:chain? false})
    (let [nodes (vec (repeatedly (inc n) #(tu/tmp-ind "Node")))]
      (doseq [[a b] (partition 2 1 nodes)]
        (v/assert kb (list link a b) 'CxUniverse {:chain? false}))
      (v/assert kb (list tagged (list NextFn (first nodes))) 'CxUniverse {:chain? false}))
    [nextOf tagged]))

(defn- nesting-recorder
  "A wrapper for `chain/chain` that keeps the number of runs open in `depth`."
  [depth]
  (let [run chain/chain]
    (fn [kb seed opts]
      (swap! depth inc)
      (try (run kb seed opts) (finally (swap! depth dec))))))

(tu/deftest-kb a-minted-term-is-chained-by-the-run-that-minted-it
  ;; Forty mints, each joined by the firing after it, in the one run `forward-chain`
  ;; starts: no chain opens inside another.
  (let [[nextOf tagged] (minting-line! kb 40)
        depth (atom 0)
        most  (atom 0)
        runs  (:runs (v/chain-stats kb) 0)
        r     (with-redefs [chain/chain (let [run (nesting-recorder depth)]
                                          (fn [kb seed opts]
                                            (swap! most max (inc @depth))
                                            (run kb seed opts)))]
                (v/forward-chain kb {}))]
    (is (not (:truncated? r)))
    (is (= 41 (v/count-with-functor kb nextOf) (v/count-with-functor kb tagged)))
    (is (= 1 @most))
    (is (= (inc runs) (:runs (v/chain-stats kb))))))

(tu/deftest-kb a-recursive-mint-past-the-term-bound-is-refused-at-max-derivations
  ;; With the term bound off, `(result SuccFn num)` stores `(num K)` as a premise of each
  ;; mint, so no bound but `:max-derivations` ends the write.  The run counts what each
  ;; mint writes against it, and the refusal takes back every mint.
  (tu/with-terms [SuccFn num]
    (v/assert kb (list 'reifiable_function SuccFn) 'CxUniverse)
    (v/assert kb (list 'result SuccFn num) 'CxUniverse)
    (v/assert kb (fwd [(list num '?x)] (list num (list SuccFn '?x))) 'CxUniverse)
    (let [runs (:runs (v/chain-stats kb) 0)
          e    (try (v/assert kb (list num (tu/tmp-ind "Zero")) 'CxUniverse
                              {:max-derivations 30 :max-term-depth nil})
                    (catch clojure.lang.ExceptionInfo e e))]
      (is (= {:type :interrupted :bound :max-derivations} (select-keys (ex-data e) [:type :bound])))
      (is (= (inc runs) (:runs (v/chain-stats kb))))
      (is (zero? (v/count-with-functor kb num))))))

(tu/deftest-kb a-bound-ends-a-run-chaining-minted-terms-and-keeps-what-it-placed
  ;; Stopped at the sixth of twelve mints under `:on-stop :keep`.  Nothing a mint's assert
  ;; wrote is taken back, no firing is made past the bound, and a later unbounded run
  ;; completes the closure from what the stopped one kept.  The deadline row moves the
  ;; clock past `:max-ms` at the same point, through the instant every deadline is checked
  ;; against.
  (doseq [[how opts clock] [[:stop? (fn [past?] {:progress-every-ms 0 :stop? past? :on-stop :keep})
                             (fn [_ now] now)]
                            [:max-ms (fn [_] {:max-ms 60000 :on-stop :keep})
                             (fn [past? now] #(if (past?) (+ (long (now)) 3600000000000) (now)))]]]
    (let [[nextOf tagged] (minting-line! kb 12)
          seen  (atom nil)
          past? #(let [c (v/count-with-functor kb nextOf)]
                   (when (>= c 6)
                     (swap! seen (fn [s] (or s {:nextOf c})))
                     true))
          r     (with-redefs [budget/now (clock past? budget/now)]
                  (v/forward-chain kb (opts past?)))]
      (testing (str how)
        (is (= {:truncated? true :bound how} (select-keys r [:truncated? :bound])))
        (is (= (:nextOf @seen) (v/count-with-functor kb nextOf))
            "every term minted before the bound is kept, and none is minted after it")
        (is (= (:nextOf @seen) (v/count-with-functor kb tagged)))
        (is (empty? (v/violations kb)))
        (is (not (:truncated? (v/forward-chain kb {}))))
        (is (= 13 (v/count-with-functor kb nextOf) (v/count-with-functor kb tagged))
            "a run from what it kept reaches the whole closure")))))

(tu/deftest-kb a-bound-ends-a-join-under-way
  ;; One rule joining three extents of eight under a computed guard that rejects every
  ;; row: 512 rows, none of which fires, so neither a firing nor the agenda loop is reached
  ;; while the join runs.  Stopped at the fortieth row, the guard is asked no more.
  (tu/with-terms [p q r okRow joined]
    (let [asks (atom 0)]
      (v/add-prover kb (v/prover {:applicable?        (fn [_ g _] (and (seq? g) (= okRow (first g))))
                                  :solve-with-support (fn [_ _ _] (swap! asks inc) [])
                                  :support-functors   #{okRow}
                                  :support-sources    #{p}}))
      (v/assert kb (fwd [(list p '?x) (list q '?y) (list r '?z) (list okRow '?x '?y '?z)]
                        (list joined '?x '?y '?z))
                'CxUniverse {:chain? false})
      (doseq [pred [p q r], _ (range 8)]
        (v/assert kb (list pred (tu/tmp-ind "Row")) 'CxUniverse {:chain? false}))
      (let [r (v/forward-chain kb {:progress-every-ms 0 :stop? #(>= @asks 40) :on-stop :keep})]
        (is (:truncated? r))
        (is (= 40 @asks))
        (is (zero? (v/count-with-functor kb joined)))))))

;; ---- an interrupted write rolls back -----------------------------------------
;;
;; A write the caller's bound ends throws `:interrupted` and leaves the store, belief and
;; the refusal record as it found them (docs/inference.md, "Stopping a run").

(defn- base-line!
  "The base half of `line-graph!`'s closure over a line of `n` edges, chained.  Returns
  `[edge path ctx rule]`, `rule` the transitive half, not yet asserted."
  [kb n]
  (let [edge (tu/tmp-pred "edge"), path (tu/tmp-pred "path"), ctx (tu/tmp-ctx "Graph")
        nodes (vec (repeatedly (inc n) #(tu/tmp-ind "N")))]
    (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
    (v/assert kb (fwd [(list edge '?x '?y)] (list path '?x '?y)) ctx)
    (doseq [[a b] (partition 2 1 nodes)]
      (v/assert kb (list edge a b) ctx))
    [edge path ctx (fwd [(list edge '?x '?y) (list path '?y '?z)] (list path '?x '?z))]))

(defn- kb-state
  "What an interrupted write must leave as it found it: each stored sentex's record (a
  rule's slots included) and written spellings, the stored justifications, belief, the
  refusal record, the violations ledger and the mint queues."
  [kb]
  {:rows           (into {} (map (fn [h] [h [(p/get-sentex (:records kb) h)
                                             (integrate/spellings kb h)]]))
                         (tu/sentex-ids kb))
   :justifications (tu/justification-ids kb)
   :believed       (set (jtms/in-datums (reasoning/tms kb)))
   :refused        @(reasoning/refused kb)
   :violations     @(reasoning/violations kb)
   :queues         (select-keys @(reasoning/mint-queues kb) [:owed :defer-next])})

(defn- interruption
  "`(f)`'s `:interrupted` refusal as `[bound rolled-back?]`, or `[:returned]`."
  [f]
  (try (f) [:returned]
       (catch clojure.lang.ExceptionInfo e
         (let [d (ex-data e)]
           (if (= :interrupted (:type d)) [(:bound d) (boolean (:rolled-back d))] (throw e))))))

(tu/deftest-kb an-interrupted-write-leaves-the-kb-as-it-found-it
  ;; The transitive half of a closure over a line whose base half is chained: asserting
  ;; it makes 45 firings, and each row ends it after the tenth.  The `:max-ms` row moves
  ;; the clock past the deadline at that point, through the instant every deadline is
  ;; checked against.
  (let [[_ path ctx rule] (base-line! kb 10)]
    (let [n (v/count-with-functor kb path)]
      (doseq [[how write clock]
              [[:stop? #(v/assert kb rule ctx {:progress-every-ms 0 :stop? %}) (fn [_ now] now)]
               [:max-ms (fn [_] (v/assert kb rule ctx {:max-ms 60000}))
                (fn [past? now] #(if (past?) (+ (long (now)) 3600000000000) (now)))]
               [:max-derivations (fn [_] (v/assert kb rule ctx {:max-derivations 10}))
                (fn [_ now] now)]
               [:stop? #(v/edit! kb {:add [[rule ctx]]} {:progress-every-ms 0 :stop? %})
                (fn [_ now] now)]]]
        (let [before (kb-state kb)
              past?  #(>= (v/count-with-functor kb path) (+ n 10))]
          (testing (name how)
            (is (= how (first (with-redefs [budget/now (clock past? budget/now)]
                                (interruption #(write past?))))))
            (is (= before (kb-state kb)))))))))

(tu/deftest-kb a-write-deriving-exactly-its-max-derivations-stores-its-closure
  ;; `(p Rex)` concludes `(q Rex)` and `(r Rex)`, and both go back on the agenda.  A cap
  ;; of 2 leaves nothing unmade; a cap of 1 leaves `(r Rex)` unmade.
  (tu/with-terms [p q r Rex]
    (v/assert kb (fwd [(list p '?x)] (list q '?x)) 'CxUniverse)
    (v/assert kb (fwd [(list q '?x)] (list r '?x)) 'CxUniverse)
    (let [before (kb-state kb)]
      (is (= :max-derivations
             (first (interruption #(v/assert kb (list p Rex) 'CxUniverse {:max-derivations 1})))))
      (is (= before (kb-state kb))))
    (is (= [:returned] (interruption #(v/assert kb (list p Rex) 'CxUniverse {:max-derivations 2}))))
    (is (= [1 1] (mapv #(v/count-with-functor kb %) [q r])))))

(tu/deftest-kb a-write-s-chain-bounds-reach-its-settle-s-re-chain-in-either-order
  ;; `(num Zero)` in CxB meets the rule in CxA only through `(genlCx CxB CxA)`.  With the
  ;; fact last, the write's own run derives the closure; with the edge last, the write's
  ;; settle re-chains the fact over the move, and `assert-many`'s closing settle does.
  ;; `assert-many`'s closing settle drops `:max-derivations`, so that row reads no cap.
  (doseq [arrives [:fact :edge :edge-in-assert-many]]
    (tu/with-terms [SuccFn num Zero CxA CxB]
      (let [fact  (list num Zero)
            edge  (list 'genlCx CxB CxA)
            bound (+ 4 (:max-term-depth v/default-chain-opts))
            write (fn [opts] (case arrives
                               :fact                (v/assert kb fact CxB opts)
                               :edge                (v/assert kb edge 'CxUniverse opts)
                               :edge-in-assert-many (v/assert-many kb [edge] 'CxUniverse opts)))]
        (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'reifiable_function SuccFn) 'CxUniverse)
        (v/assert kb (fwd [(list num '?x)] (list num (list SuccFn '?x))) CxA)
        (if (= :fact arrives) (v/assert kb edge 'CxUniverse) (v/assert kb fact CxB))
        (testing (name arrives)
          (when-not (= :edge-in-assert-many arrives)
            (let [before (kb-state kb)]
              (is (= :max-derivations (first (interruption #(write {:max-derivations 3})))))
              (is (= before (kb-state kb)))))
          (write {:max-term-depth bound})
          (is (= (inc bound) (v/count-with-functor kb num)) "Zero and one constant per level"))))))

(tu/deftest-kb an-interrupted-batch-of-asserts-keeps-the-sentences-before-the-cut
  (let [[edge path ctx] (line-graph! kb 0)
        nodes (vec (repeatedly 4 #(tu/tmp-ind "N")))
        _     (v/forward-chain kb {})
        e     (try (v/assert-many kb (map (fn [[a b]] (list edge a b)) (partition 2 1 nodes)) ctx
                                  {:progress-every-ms 0
                                   :stop? #(>= (v/count-with-functor kb edge) 2)})
                   (catch clojure.lang.ExceptionInfo e e))
        stored (:stored (ex-data e))]
    (is (= :interrupted (:type (ex-data e))))
    (is (< (count stored) 3))
    (is (= (count stored) (v/count-with-functor kb edge)))
    (is (every? #(v/in? kb %) stored))
    (is (= (quot (* (count stored) (inc (count stored))) 2) (v/count-with-functor kb path))
        "each stored edge keeps its whole closure")))

(tu/deftest-kb an-interrupted-bulk-batch-rolls-back-the-sentence-in-flight
  ;; Two rules and a line of ten edges in one `assert-many` under `*bulk-load?*`.  The
  ;; k-th edge places k paths, so the first six place 21 and the bound is reached inside
  ;; the seventh edge's chain, at the 24th path.
  (let [edge  (tu/tmp-pred "edge"), path (tu/tmp-pred "path"), ctx (tu/tmp-ctx "Graph")
        nodes (vec (repeatedly 11 #(tu/tmp-ind "N")))
        edges (mapv (fn [[a b]] (list edge a b)) (partition 2 1 nodes))
        _     (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
        before (tu/sentex-ids kb)
        e     (try (binding [v/*bulk-load?* true]
                     (v/assert-many kb (into [(fwd [(list edge '?x '?y)] (list path '?x '?y))
                                              (fwd [(list edge '?x '?y) (list path '?y '?z)]
                                                   (list path '?x '?z))]
                                             edges)
                                    ctx {:progress-every-ms 0
                                         :stop? #(>= (v/count-with-functor kb path) 24)}))
                   (catch clojure.lang.ExceptionInfo e e))
        added (remove before (tu/sentex-ids kb))]
    (is (= {:type :interrupted :bound :stop?} (select-keys (ex-data e) [:type :bound])))
    (is (= 8 (count (:stored (ex-data e)))) "the two rules and the six edges before the cut")
    (is (= 6 (v/count-with-functor kb edge)))
    (is (= 21 (v/count-with-functor kb path)) "each stored edge keeps its whole closure")
    (is (nil? (v/handle-of kb (nth edges 6) ctx)) "the edge in flight left no record")
    (is (= (+ 8 21) (count added)))
    (is (every? #(v/in? kb %) added) "the closing settle ran over what the batch kept")))

(tu/deftest-kb an-interrupted-batch-keeps-the-closure-its-first-sentence-has-alone
  ;; The edge's `genlCx` move is settled by the batch, after the second sentence's chain
  ;; reaches the bound; the rollback of that sentence settles first, and runs the move's
  ;; re-chain to its end.
  (tu/with-terms [pp qq rr ss Aa Bb CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (fwd [(list pp '?x)] (list qq '?x)) CxA)
    (v/assert kb (list pp Aa) CxB)
    (v/assert kb (fwd [(list rr '?x)] (list ss '?x)) 'CxUniverse)
    (let [edge    (list 'genlCx CxB CxA)
          closure #(set (map :sentence (v/sentexes-with-functor kb qq {:believed? true})))
          e       (try (v/assert-many kb [edge (list rr Bb)] 'CxUniverse
                                      {:progress-every-ms 0
                                       :stop? #(pos? (v/count-with-functor kb rr))})
                       (catch clojure.lang.ExceptionInfo e e))
          bounded (closure)]
      (is (= [:interrupted 1] [(:type (ex-data e)) (count (:stored (ex-data e)))]))
      (is (zero? (v/count-with-functor kb rr)))
      (v/retract! kb (first (:stored (ex-data e))))
      (is (empty? (closure)))
      (v/assert-many kb [edge] 'CxUniverse)
      (is (= #{(list qq Aa)} (closure) bounded)))))

(tu/deftest-kb a-throwing-progress-callback-rolls-the-write-back
  (let [[_ _ ctx rule] (base-line! kb 10)
        before (kb-state kb)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"stop here"
                          (v/assert kb rule ctx {:progress-every-ms 0
                                                 :on-progress (fn [_] (throw (ex-info "stop here" {})))})))
    (is (= before (kb-state kb)))))

(tu/deftest-kb a-stopped-forward-chain-leaves-the-kb-as-it-found-it
  ;; With the term bound off, each firing of `(num ?x)` → `(num (SuccFn ?x))` mints a term
  ;; whose mint stores `(num K)` as a premise, so the run has no end of its own.  Each row
  ;; ends it at the tenth `num`; the `:max-ms` row moves the clock past the deadline there.
  (tu/with-terms [SuccFn num]
    (v/assert kb (list 'reifiable_function SuccFn) 'CxUniverse)
    (v/assert kb (list 'result SuccFn num) 'CxUniverse)
    (v/assert kb (fwd [(list num '?x)] (list num (list SuccFn '?x))) 'CxUniverse)
    (v/assert kb (list num (tu/tmp-ind "Zero")) 'CxUniverse {:chain? false})
    (let [base  {:max-term-depth nil :progress-every-ms 0}
          past? #(>= (v/count-with-functor kb num) 10)]
      (doseq [[how opts clock]
              [[:stop? #(assoc base :stop? %) (fn [_ now] now)]
               [:max-ms (fn [_] (assoc base :max-ms 60000))
                (fn [past? now] #(if (past?) (+ (long (now)) 3600000000000) (now)))]
               [:max-derivations (fn [_] (assoc base :max-derivations 10)) (fn [_ now] now)]
               [:on-progress
                (fn [past?] (assoc base :on-progress
                                   (fn [_] (when (past?) (throw (ex-info "stop here" {}))))))
                (fn [_ now] now)]]]
        (let [before (kb-state kb)]
          (testing (name how)
            (is (= [how false] (with-redefs [budget/now (clock past? budget/now)]
                                 (interruption #(v/forward-chain kb (opts past?))))))
            (is (= 1 (v/count-with-functor kb num)))
            (is (= before (kb-state kb)))))))))

(tu/deftest-kb a-stopped-forward-chain-places-a-defeat-only-under-keep
  ;; The run concludes `(not (flies Tweety))` from monotonic content, against the default
  ;; `(flies Tweety)` stored before it, and is stopped at the sixth mint along
  ;; `minting-line!`.  Belief moves at the settle and not inside the run, so at either stop
  ;; the denial is stored and `(flies Tweety)` is still IN.  Under the default the rollback
  ;; removes the denial before its own settle, so that settle leaves the default believed;
  ;; a denial left stored would take it out there, as the settle under `:keep` does.
  (tu/with-terms [flies penguin Tweety]
    (v/assert kb (fwd [(list penguin '?x)] (list 'not (list flies '?x))) 'CxUniverse
              {:strength :monotonic :chain? false})
    (v/assert kb (list penguin Tweety) 'CxUniverse {:strength :monotonic :chain? false})
    (let [hf       (v/assert kb (list flies Tweety) 'CxUniverse {:chain? false})
          [nextOf] (minting-line! kb 12)
          denial   (list 'not (list flies Tweety))
          denied?  #(some? (v/handle-of kb denial 'CxUniverse))
          at       (atom [])
          opts     (fn [on-stop]
                     (cond-> {:progress-every-ms 0
                              :stop? #(when (>= (v/count-with-functor kb nextOf) 6)
                                        (swap! at conj [(denied?) (v/in? kb hf)])
                                        true)}
                       on-stop (assoc :on-stop on-stop)))
          before   (kb-state kb)]
      (is (v/in? kb hf))
      (is (= [:stop? false] (interruption #(v/forward-chain kb (opts nil)))))
      (is (not (denied?)))
      (is (v/in? kb hf))
      (is (= before (kb-state kb)))
      (is (= {:truncated? true :bound :stop?}
             (select-keys (v/forward-chain kb (opts :keep)) [:truncated? :bound])))
      (is (= [[true true] [true true]] @at)
          "both runs had placed the denial, and believed the default, when they stopped")
      (is (denied?))
      (is (not (v/in? kb hf))))))

(tu/deftest-kb an-interrupted-rule-re-assert-leaves-the-rule-s-engines-as-they-were
  ;; Re-asserting a backward rule for the forward engine rewrites the stored rule's
  ;; engines in place, and the forward run its new engine starts is stopped at the second
  ;; derivation.  The rollback puts the engines back, and no forward conclusion stays.
  (tu/with-terms [edgeP pathP CxProbe]
    (v/assert kb (list 'genlCx CxProbe 'CxUniverse) 'CxUniverse)
    (doseq [[a b] (partition 2 1 (repeatedly 7 #(tu/tmp-ind "N")))]
      (v/assert kb (list edgeP a b) CxProbe))
    (let [rh     (v/assert-rule kb [(list edgeP '?x '?y)] (list pathP '?x '?y) CxProbe
                                {:direction :backward})
          before (kb-state kb)]
      (is (= #{:backward} (:engines (p/get-sentex (:records kb) rh))))
      (is (= [:max-derivations false]
             (interruption #(v/assert-rule kb [(list edgeP '?x '?y)] (list pathP '?x '?y) CxProbe
                                           {:direction :forward :max-derivations 2}))))
      (is (= #{:backward} (:engines (p/get-sentex (:records kb) rh))))
      (is (zero? (v/count-with-functor kb pathP)))
      (is (= before (kb-state kb))))))

(tu/deftest-kb an-arithmetic-recursion-is-cut-by-no-default
  ;; `(count ?n)` → `(count ?n+1)` builds no term, so the term-nesting bound never applies
  ;; and the run goes on until the caller stops it, past the 1000th conclusion.
  (tu/with-terms [cnt]
    (v/assert kb (fwd [(list cnt '?n) (list 'evaluate '?m (list '+ '?n 1))] (list cnt '?m))
              'CxUniverse)
    (let [before  (kb-state kb)
          reached (atom 0)]
      (is (= [:stop? false]
             (interruption #(v/assert kb (list cnt 0) 'CxUniverse
                                      {:progress-every-ms 0
                                       :stop? (fn [] (>= (reset! reached (v/count-with-functor kb cnt))
                                                         1000))}))))
      (is (<= 1000 @reached))
      (is (= before (kb-state kb))))))

(tu/deftest-kb a-chaining-write-refuses-to-go-on-over-a-nearly-full-heap
  (let [[_ _ ctx rule] (base-line! kb 4)
        before (kb-state kb)]
    (is (= [:heap false]
           (with-redefs [caches/heap-critical? (constantly true)]
             (interruption #(v/assert kb rule ctx)))))
    (is (= before (kb-state kb)))))

(defn- with-full-heap
  "`(f)` with the heap mark's flag set by the listener body (`set-mark!`, passed to `f`) and
  the armed pool reading 95% full, so `heap-critical?` holds until the flag is cleared at
  the end."
  [f]
  (let [critical @#'caches/critical
        pool     (:heap-mark (caches/memory-guard))
        set-mark! #(@#'caches/on-threshold
                    java.lang.management.MemoryNotificationInfo/MEMORY_COLLECTION_THRESHOLD_EXCEEDED
                    pool)]
    (try (with-redefs-fn {#'caches/pool-fraction (constantly 0.95)}
           #(f set-mark!))
         (finally (vreset! critical false)))))

(tu/deftest-kb a-kb-open-kb-opened-refuses-a-chaining-write-over-a-full-heap-with-no-guard
  (is (false? (:installed? (caches/memory-guard))))
  (is (some? (:heap-mark (caches/memory-guard))) "open-kb armed the heap mark")
  (let [[_ _ ctx rule] (base-line! kb 4)
        before (kb-state kb)]
    (is (= [:heap false]
           (with-full-heap (fn [set-mark!] (set-mark!) (interruption #(v/assert kb rule ctx))))))
    (is (= before (kb-state kb)))))

(tu/deftest-kb the-heap-mark-stops-a-run-inside-a-datum-s-firings
  ;; One `(trig T)` datum joins 30 `q` facts and fires 30 times.  The progress callback sets
  ;; the mark once three conclusions are placed; the next firing refuses, before the datum
  ;; ends and the agenda loop reads the mark again.
  (tu/with-terms [trig q r T CxHeap]
    (v/assert kb (list 'genlCx CxHeap 'CxUniverse) 'CxUniverse)
    (doseq [_ (range 30)] (v/assert kb (list q (tu/tmp-ind "A")) CxHeap))
    (v/assert kb (fwd [(list trig '?t) (list q '?y)] (list r '?y)) CxHeap)
    (let [before (kb-state kb)
          marked (atom nil)
          seen   (atom 0)]
      (is (= [:heap false]
             (with-full-heap
               (fn [set-mark!]
                 (interruption
                  #(v/assert kb (list trig T) CxHeap
                             {:progress-every-ms 0
                              :on-progress (fn [{:keys [derived]}]
                                             (swap! seen max derived)
                                             (when (and (nil? @marked) (>= derived 3))
                                               (reset! marked derived)
                                               (set-mark!)))}))))))
      (is (= @marked @seen) "no firing after the mark placed a conclusion")
      (is (< @seen 30))
      (is (= before (kb-state kb))))))

(tu/deftest-kb an-unchained-batch-stops-before-the-next-fact-over-a-nearly-full-heap
  ;; Under `:chain? false` no agenda loop runs, so nothing in an assert reads the mark.  The
  ;; mark is set as the batch pulls its second sentence, and the batch reads it before
  ;; asserting that sentence.
  (tu/with-terms [rr Aa Bb Cc]
    (let [e (with-full-heap
              (fn [set-mark!]
                (try (v/assert-many kb (cons (list rr Aa)
                                             (lazy-seq (set-mark!) [(list rr Bb) (list rr Cc)]))
                                    'CxUniverse {:chain? false})
                     (catch clojure.lang.ExceptionInfo e e))))]
      (is (= [:interrupted :heap] ((juxt :type :bound) (ex-data e))))
      (is (= 1 (count (:stored (ex-data e)))))
      (is (some? (v/handle-of kb (list rr Aa) 'CxUniverse)))
      (is (nil? (v/handle-of kb (list rr Bb) 'CxUniverse))))))

(tu/deftest-kb a-removal-runs-to-its-end-over-a-nearly-full-heap
  ;; Retracting the `genlCx` edge CxB → CxA sweeps `(qq Aa)` in CxB, whose placement names
  ;; the edge.  With the route CxB → CxM → CxA asserted after the edge, the settle
  ;; re-chains `(qq Aa)` through that route.  Outside a rollback scope the heap mark stops
  ;; nothing, so the removal and its settle complete as they do under an empty heap.
  (doseq [[how remove!] [[:retract! #(v/retract! kb %)] [:edit! #(v/edit! kb {:remove [%]})]]
          route?        [false true]]
    (tu/with-terms [pp qq Aa CxA CxB CxM]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (fwd [(list pp '?x)] (list qq '?x)) CxA)
      (v/assert kb (list pp Aa) CxB)
      (let [before (kb-state kb)
            edge   (list 'genlCx CxB CxA)
            h      (v/assert kb edge 'CxUniverse)]
        (when route?
          (v/assert kb (list 'genlCx CxM CxA) 'CxUniverse)
          (v/assert kb (list 'genlCx CxB CxM) 'CxUniverse))
        (testing (str (name how) (when route? " with a surviving route"))
          (is (v/in? kb (v/handle-of kb (list qq Aa) CxB)))
          (is (= [true :returned]
                 (with-full-heap
                   (fn [set-mark!]
                     (set-mark!)
                     [(caches/heap-critical?) (do (remove! h) :returned)]))))
          (is (nil? (v/handle-of kb edge 'CxUniverse)))
          (if route?
            (is (v/in? kb (v/handle-of kb (list qq Aa) CxB)) "the settle's re-chain ran")
            (is (= before (kb-state kb)))))))))

(tu/deftest-kb forward-chain-over-a-nearly-full-heap-rolls-back-under-either-on-stop
  ;; The progress callback sets the mark once six of twelve terms are minted, and the next
  ;; check throws `:heap`.  The run is taken back under `:on-stop :keep` as under the
  ;; default, and once the mark is cleared an unbounded run completes the closure.
  (doseq [on-stop [nil :keep]]
    (let [[nextOf tagged] (minting-line! kb 12)
          before (kb-state kb)
          seen   (atom nil)]
      (testing (str (or on-stop "the default"))
        (is (= [:heap false]
               (with-full-heap
                 (fn [set-mark!]
                   (interruption
                    #(v/forward-chain
                      kb (cond-> {:progress-every-ms 0
                                  :on-progress
                                  (fn [_]
                                    (let [c (v/count-with-functor kb nextOf)]
                                      (when (and (nil? @seen) (>= c 6))
                                        (reset! seen c)
                                        (set-mark!))))}
                           on-stop (assoc :on-stop on-stop))))))))
        (is (some? @seen))
        (is (= before (kb-state kb)))
        (is (= {:truncated? false} (select-keys (v/forward-chain kb {}) [:truncated? :bound])))
        (is (= 13 (v/count-with-functor kb nextOf) (v/count-with-functor kb tagged)))))))

;; ---- the accepted option keys ---------------------------------------------

(tu/deftest-kb a-forward-chain-option-nothing-reads-is-refused
  ;; Every key `forward-chain` takes sets a bound or reports progress on one, so the
  ;; silent-default failure is a run with no ceiling: `{:max-derivation n}` reads as no
  ;; key at all and the fixpoint runs unbounded — the exact run the option was written
  ;; to prevent.  Wire-reachable, too: the daemon's `:forward-chain` op passes its args
  ;; straight through.
  (testing "the singular typo is refused, naming the plural it meant"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (v/forward-chain kb {:max-derivation 5})))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= [:max-derivation] (:unknown (ex-data e))))
      (is (re-find #":max-derivations" (ex-message e))
          "the message lists what forward-chain does read")))
  (testing "a non-map opts is refused rather than read as no bounds"
    ;; The keyword is the point — the refusal is what this asserts — so the
    ;; type mismatch clj-kondo sees is the test's subject, not a defect.
    #_{:clj-kondo/ignore [:type-mismatch]}
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a map"
                          (v/forward-chain kb :max-derivations))))
  (testing "the accepted keys still run"
    (let [r (v/forward-chain kb {:max-depth 2 :max-derivations 10
                                 :progress-every-ms 1000 :on-progress (fn [_])})]
      (is (contains? r :derived)))))

(tu/deftest-kb a-stopped-run-that-re-decides-a-value-copy-leaves-the-kb-as-it-found-it
  ;; `(likes Tom K)` and a rule naming K, K minted for `(MomFn Muffet)`, take copies
  ;; naming `Mary` in CxStory from the `:default` `(momOf Muffet Mary)` there.  A run
  ;; firing `(stepOf ?x ?y)` → `(momOf ?x ?y)` stores a second value, `Jane`, so CxStory
  ;; owes neither copy.  Each row stops the run at the next datum, after the value sync
  ;; has re-decided K.  The copies are below the write's mark, so the rollback restores
  ;; them only if the run left them in place; the settle of an unbounded run drops them.
  (tu/with-terms [MomFn momOf stepOf Muffet Mary Jane Tom likes fond seen CxStory]
    (let [app  (list MomFn Muffet)
          fact (list stepOf Muffet Jane)]
      (v/assert kb (list 'reifiable_function MomFn) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'functionCorrespondingPredicate MomFn momOf 2) 'CxUniverse)
      (v/assert kb (list momOf Muffet Mary) CxStory)
      (v/assert kb (list likes Tom app) 'CxUniverse)
      (v/assert kb (fwd [(list likes '?x app)] (list fond '?x)) 'CxUniverse)
      (v/assert kb (fwd [(list stepOf '?x '?y)] (list momOf '?x '?y)) CxStory {:chain? false})
      (v/assert kb (fwd [(list momOf '?x '?y)] (list seen '?y)) CxStory {:chain? false})
      (let [copies   #(into #{} (keep (fn [s] (v/handle-of kb s CxStory)))
                            [(list likes Tom Mary) (fwd [(list likes '?x Mary)] (list fond '?x))])
            stored   (copies)
            at-stop  (atom [])
            stop?    #(when (v/handle-of kb (list momOf Muffet Jane) CxStory)
                        (swap! at-stop conj (copies))
                        true)]
        (is (= 2 (count stored)))
        (doseq [[how write] [[:forward-chain
                              (fn []
                                (v/assert kb fact CxStory {:chain? false})
                                [(kb-state kb)
                                 (interruption #(v/forward-chain kb {:progress-every-ms 0
                                                                     :stop? stop?}))])]
                             [:assert
                              (fn []
                                [(kb-state kb)
                                 (interruption #(v/assert kb fact CxStory {:progress-every-ms 0
                                                                           :stop? stop?}))])]]]
          (testing (name how)
            (let [[before stopped] (write)]
              (is (= [:stop? false] stopped))
              (is (= before (kb-state kb)))))
          (some->> (v/handle-of kb fact CxStory) (v/retract! kb)))
        (is (= [stored stored] @at-stop) "each run had re-decided K and kept the copies")
        (v/assert kb fact CxStory {:chain? false})
        (v/forward-chain kb)
        (is (empty? (copies)) "the settle of the unbounded run drops both copies")))))
