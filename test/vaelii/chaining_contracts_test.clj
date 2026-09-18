;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.chaining-contracts-test
  "Two guards on the forward-chaining path that nothing exercised.

  `:max-derivations` is the backstop against a runaway chain that is *not* bounded
  by depth — a rule that derives ever more facts at the same depth walks straight
  past `:max-depth`.  Only the depth bound had a test, so the second `:truncated?`
  disjunct was unreachable from the suite.

  The second is the `new?` gate on the transitive re-seed, which is what keeps the
  first backstop from being the thing that ends an ordinary run — see the test."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

;; ---- :max-derivations ---------------------------------------------------

(tu/deftest-kb default-chain-opts-publishes-both-bounds
  ;; A public def with no test reference.  If the opts merge ever dropped a key, the
  ;; chain loop would compare against nil and NPE, or against a default that never
  ;; fires — this is the only thing that would notice the shape changing.
  (is (= #{:max-depth :max-derivations} (set (keys v/default-chain-opts))))
  (is (pos-int? (:max-depth v/default-chain-opts)))
  (is (pos-int? (:max-derivations v/default-chain-opts))))

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
  ;; what pins it without over-claiming.
  (tu/with-terms [edge path A B C D E CxGraph]
    (v/assert kb (list 'genlCx CxGraph 'CxUniverse) 'CxUniverse)
    (v/assert kb (fwd [(list edge '?x '?y)] (list path '?x '?y)) CxGraph)
    (v/assert kb (fwd [(list edge '?x '?y) (list path '?y '?z)]
                      (list path '?x '?z)) CxGraph)
    (doseq [[a b] [[A B] [B C] [C D] [D E]]]
      (v/assert kb (list edge a b) CxGraph {:chain? false}))
    (let [{:keys [derived truncated?]} (v/forward-chain kb {:max-derivations 2})]
      (is truncated? "the run hit the derivation backstop")
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
  ;; The `new?` gate on `special/transitive-seeds` in `place-fact-conclusion`, and the
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
  ;; is about convergence rather than about a count: ungated this reaches 500 with the
  ;; closure still unfinished, gated it stops at three.
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
;; test cannot wait out honestly — a run big enough to take seconds is a slow test, and one
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
  ;; How a loader cancels: there is no other point at which stopping a fixpoint is safe.
  ;; What had been derived stays — conclusions are placed as they are made — so the KB is
  ;; a prefix of the run, which is what `unload!` then takes down.
  (let [[_ path _] (line-graph! kb 40)
        closure    (/ (* 40 41) 2)]                  ; every ordered pair along the line
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"stop here"
                          (v/forward-chain kb {:progress-every-ms 0
                                               :on-progress (fn [_] (throw (ex-info "stop here" {})))})))
    (is (< (v/count-with-functor kb path) closure)
        "the abort landed before the closure was complete")
    (v/forward-chain kb {})
    (is (= closure (v/count-with-functor kb path))
        "and a run from what it had placed reaches the same fixpoint")))

;; ---- the opts roster ------------------------------------------------------

(tu/deftest-kb a-forward-chain-option-nothing-reads-is-refused
  ;; Every key `forward-chain` takes is a bound or the window into one, so the
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
  (testing "the rostered keys still run"
    (let [r (v/forward-chain kb {:max-depth 2 :max-derivations 10
                                 :progress-every-ms 1000 :on-progress (fn [_])})]
      (is (contains? r :derived)))))
