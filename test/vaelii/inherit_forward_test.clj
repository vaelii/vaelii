;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherit-forward-test
  "Forward chaining on a claim nobody stored.

  `(transitiveInArg largerThan 1 genl)` beside `(largerThan dog cat)` licenses
  `(largerThan chihuahua maine_coon)`, and a rule over `largerThan` has to fire on it —
  or `sentexes-matching` reads one answer out of the fixpoint while `ask` re-derives
  another through `TransitiveInArgProver`, which is the same knowledge giving two answers
  depending on which entry point the reader came in.

  What makes that possible is that an inherited claim, while it is not stored, was
  *read from* things that are: the claim that was stated, the declaration licensing the
  move, and the relation edges the reach travelled.  The firing names them, so the
  tests below are mostly about that list — `why` reads it back, retraction walks it,
  and placement is computed from it."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.settle :as settle]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private ctx 'CxUniverse)

(defn- holds?
  "Does the KB **hold** this sentence — is it in what the fixpoint derived, rather than
  what a prover would re-derive on demand?  The half of the disagreement this whole
  namespace is about."
  [kb s]
  (boolean (seq (v/sentexes-matching kb s ctx))))

(defn- kinds!
  "dog ⊃ {golden_retriever chihuahua}, cat ⊃ {maine_coon siamese}."
  [kb {:keys [dog cat gr chi mc sia]}]
  (v/with-deferred-settle kb
    (doseq [[sub sup] [[gr dog] [chi dog] [mc cat] [sia cat]]]
      (v/assert kb (list 'genl sub sup) ctx))))

(defn- preserving!
  "Both positions of `pred` preserved along genl, and the asymmetry that gives a
  converse the standing to deny an inherited claim."
  [kb pred]
  (v/with-deferred-settle kb
    (v/assert kb (list 'asymmetric pred) ctx)
    (v/assert kb (list 'transitiveInArg pred 1 'genl) ctx)
    (v/assert kb (list 'transitiveInArg pred 2 'genl) ctx)))

;; ---- the disagreement itself ---------------------------------------------

(tu/deftest-kb the-two-entry-points-give-the-same-answer
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx {:direction :forward})
    (testing "the stored antecedent, which always fired"
      (is (holds? kb (list outweighs dog_t cat_t)))
      (is (v/ask? kb (list outweighs dog_t cat_t) ctx)))
    (testing "and the inherited one, which is the point"
      (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))
      (is (v/ask? kb (list outweighs chihuahua_t maine_coon_t) ctx)))
    (testing "every tuple the claim licenses, and no tuple it does not"
      (is (= 9 (count (v/sentexes-matching kb (list outweighs '?x '?y) ctx)))
          "3 terms below-or-at dog × 3 below-or-at cat")
      (is (not (holds? kb (list outweighs maine_coon_t chihuahua_t)))
          "preservation runs down the edges, never back up them"))))

(tu/deftest-kb the-firing-names-the-claim-the-declaration-and-the-edges
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx {:direction :forward})
    (let [w (v/why kb (v/handle-of kb (list outweighs chihuahua_t maine_coon_t) ctx))
          reasons (into #{} (comp (mapcat :because) (map :sentence)) (:support w))]
      (is (:believed? w))
      (testing "the actual reasons, and the reader can read them"
        (is (contains? reasons (list largerThan dog_t cat_t)))
        (is (contains? reasons (list 'genl chihuahua_t dog_t)))
        (is (contains? reasons (list 'genl maine_coon_t cat_t))))
      (testing "and the declarations, which license the move and are as retractable"
        (is (contains? reasons (list 'transitiveInArg largerThan 1 'genl)))
        (is (contains? reasons (list 'transitiveInArg largerThan 2 'genl))))
      (testing "nothing else — a witness, not a transcript"
        (is (= 5 (count reasons)) (pr-str reasons))))))

(tu/deftest-kb a-claim-stated-at-the-tuple-is-justified-once
  ;; The diagonal.  `witness-terms` is reflexive, so the stored claim is among the
  ;; claims bearing on its own tuple — and it already has the ordinary matcher's
  ;; justification.  A second one resting on nothing new would be manufactured.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx {:direction :forward})
    (let [w (v/why kb (v/handle-of kb (list outweighs dog_t cat_t) ctx))]
      (is (= 1 (count (:support w))))
      (is (= [(list largerThan dog_t cat_t)]
             (mapv :sentence (:because (first (:support w)))))
          "the stored claim alone, with no edge and no declaration beneath it"))))

;; ---- retraction reaches it ----------------------------------------------

(tu/deftest-kb retracting-any-reason-withdraws-the-conclusion
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx {:direction :forward})
    (let [goal (list outweighs chihuahua_t maine_coon_t)]
      (doseq [reason [(list 'genl chihuahua_t dog_t)
                      (list 'genl maine_coon_t cat_t)
                      (list largerThan dog_t cat_t)
                      (list 'transitiveInArg largerThan 1 'genl)]]
        (testing (str "retracting " (pr-str reason))
          (let [h (v/handle-of kb reason ctx)]
            (v/retract! kb h)
            (is (not (holds? kb goal)))
            (v/assert kb reason ctx)
            (is (holds? kb goal) "and re-asserting brings it back")))))
    (testing "and the rule, which every firing rests on"
      (let [r (list 'set/forwardRule (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)))]
        (v/retract! kb (v/handle-of kb r ctx))
        (is (empty? (v/sentexes-matching kb (list outweighs '?x '?y) ctx)))
        (v/assert kb r ctx)
        (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))))))

(tu/deftest-kb an-untouched-pair-survives-a-retraction-that-takes-its-neighbour
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx {:direction :forward})
    (v/retract! kb (v/handle-of kb (list 'genl chihuahua_t dog_t) ctx))
    (is (not (holds? kb (list outweighs chihuahua_t maine_coon_t))))
    (is (holds? kb (list outweighs golden_retriever_t maine_coon_t))
        "the edge it did not travel is still there")
    (is (holds? kb (list outweighs dog_t cat_t)))))

;; ---- withdrawal with nothing retracted ----------------------------------

(tu/deftest-kb a-more-specific-contrary-claim-withdraws-the-conclusion
  ;; The case the antecedents cannot express: every one of them is still stored and
  ;; believed, and a claim about a *narrower* pair has undercut what they licensed.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  typicallyLargerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb typicallyLargerThan)
    (v/assert kb (list typicallyLargerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list typicallyLargerThan '?x '?y)
                       (list outweighs '?x '?y))
              ctx {:direction :forward})
    (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))
    (let [specific (list typicallyLargerThan maine_coon_t chihuahua_t)]
      (v/assert kb specific ctx)
      (testing "the general claim stops firing for that pair, and nothing was retracted"
        (is (not (holds? kb (list outweighs chihuahua_t maine_coon_t))))
        (is (not (v/ask? kb (list outweighs chihuahua_t maine_coon_t) ctx))
            "and the two entry points still agree")
        (is (v/in? kb (v/handle-of kb (list typicallyLargerThan dog_t cat_t) ctx))
            "the general claim is undercut for one pair, not defeated"))
      (testing "the pairs it says nothing about are untouched"
        (is (holds? kb (list outweighs golden_retriever_t maine_coon_t)))
        (is (holds? kb (list outweighs dog_t cat_t))))
      (testing "and the specific claim fires in its own direction"
        (is (holds? kb (list outweighs maine_coon_t chihuahua_t))))
      (testing "retracting it brings the inherited conclusion back"
        (v/retract! kb (v/handle-of kb specific ctx))
        (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))
        (is (v/ask? kb (list outweighs chihuahua_t maine_coon_t) ctx))))))

;; ---- the relation is a parameter ----------------------------------------

(tu/deftest-kb a-fact-relation-carries-a-firing-the-same-way
  ;; No types in sight: the reach is walked over stored `partOf` facts, and the
  ;; justification names those facts and the `(transitive partOf)` that licensed
  ;; closing them.
  (tu/with-terms [partOf needs_maintenance schedule Car Engine Piston]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive partOf) ctx)
      (v/assert kb (list 'transitiveInArg needs_maintenance 1 partOf) ctx)
      (v/assert kb (list partOf Engine Car) ctx)
      (v/assert kb (list partOf Piston Engine) ctx))
    (v/assert kb (list needs_maintenance Car) ctx)
    (v/assert kb (list 'implies (list needs_maintenance '?x) (list schedule '?x)) ctx {:direction :forward})
    (is (holds? kb (list schedule Piston)) "two hops down the part chain")
    (is (v/ask? kb (list schedule Piston) ctx))
    (let [reasons (into #{}
                        (comp (mapcat :because) (map :sentence))
                        (:support (v/why kb (v/handle-of kb (list schedule Piston) ctx))))]
      (is (contains? reasons (list needs_maintenance Car)))
      (is (contains? reasons (list partOf Piston Engine)))
      (is (contains? reasons (list partOf Engine Car)))
      (is (contains? reasons (list 'transitive partOf))
          "read at use, so a firing that rests on it says so"))
    (testing "and withdrawing the transitivity withdraws what it closed"
      (v/retract! kb (v/handle-of kb (list 'transitive partOf) ctx))
      (is (not (holds? kb (list schedule Piston))))
      (is (holds? kb (list schedule Car)) "the stated claim is untouched"))))

(tu/deftest-kb a-declaration-derived-inside-a-run-licenses-the-joins-after-it
  ;; The forward path gates every preserved-antecedent question on "does this KB
  ;; declare any preservation at all", cached per chaining run
  ;; (`chain/*declarations-cell*`).  A run can *derive* the declaration — here one fact
  ;; fires two rules that conclude both `transitiveInArg`s — and everything the same run
  ;; joins after that placement has to see it: the declaration datum's own re-join of the
  ;; rules it moved, and any later datum's ordinary trigger.  A cache read once at the
  ;; start of the run and never forgotten answers "none" to both.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs preservesBoth]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (let [quiet {:chain? false}
          _     (v/assert kb (list 'asymmetric largerThan) ctx quiet)
          _     (v/assert kb (list largerThan dog_t cat_t) ctx quiet)
          rh    (v/assert kb (list 'set/forwardRule (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)))
                          ctx quiet)
          _     (v/assert kb (list 'set/forwardRule (list 'implies (list preservesBoth '?p)
                                                          (list 'transitiveInArg '?p 1 'genl))) ctx quiet)
          _     (v/assert kb (list 'set/forwardRule (list 'implies (list preservesBoth '?p)
                                                          (list 'transitiveInArg '?p 2 'genl))) ctx quiet)
          fh    (v/assert kb (list preservesBoth largerThan) ctx quiet)]
      (testing "nothing has chained yet"
        (is (not (holds? kb (list outweighs dog_t cat_t)))))
      ;; One run, seeded in this order: the rule datum joins first and asks the gate
      ;; while no declaration exists; the fact datum then derives both declarations,
      ;; whose own datums re-join the rule — under the same run's cache.
      (chain/chain-all kb [rh fh] nil)
      (settle/settle kb)
      (testing "the declarations were derived inside the run"
        (is (holds? kb (list 'transitiveInArg largerThan 1 'genl)))
        (is (holds? kb (list 'transitiveInArg largerThan 2 'genl))))
      (testing "and the joins after them inherit"
        (is (holds? kb (list outweighs dog_t cat_t)))
        (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))
        (is (= 9 (count (v/sentexes-matching kb (list outweighs '?x '?y) ctx))))))))

(tu/deftest-kb the-inverse-declaration-fires-upward
  (tu/with-terms [dog_t animal_t thing_t hasA aboutIt]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl animal_t thing_t) ctx)
      (v/assert kb (list 'transitiveInArgInverse hasA 1 'genl) ctx))
    (v/assert kb (list hasA dog_t) ctx)
    (v/assert kb (list 'implies (list hasA '?x) (list aboutIt '?x)) ctx {:direction :forward})
    (is (holds? kb (list aboutIt animal_t)) "one edge up")
    (is (holds? kb (list aboutIt thing_t)) "and two")
    (is (holds? kb (list aboutIt dog_t)) "the stated one, by the ordinary matcher")))

(tu/deftest-kb a-context-argument-carries-a-firing-down-the-lattice
  ;; The relation can be the context hierarchy: preserved along `genlCx`, a claim
  ;; naming a wide context fires for the contexts below it, off the same cached closure
  ;; the backward entry point walks (`inherit_test`).
  (tu/with-terms [appliesIn noticed TheDecree CxWide CxNarrow]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlCx CxWide ctx) ctx)
      (v/assert kb (list 'genlCx CxNarrow CxWide) ctx)
      (v/assert kb (list 'transitiveInArg appliesIn 2 'genlCx) ctx))
    (v/assert kb (list appliesIn TheDecree CxWide) ctx)
    (v/assert kb (list 'implies (list appliesIn TheDecree '?c) (list noticed '?c)) ctx {:direction :forward})
    (testing "the subcontext, by inheritance — and both entry points agree on it"
      (is (holds? kb (list noticed CxNarrow)))
      (is (v/ask? kb (list noticed CxNarrow) ctx)))
    (testing "the stated one, by the ordinary matcher"
      (is (holds? kb (list noticed CxWide)))
      (is (v/ask? kb (list noticed CxWide) ctx)))
    (testing "and nothing upward, through either entry point"
      (is (not (holds? kb (list noticed ctx))))
      (is (not (v/ask? kb (list noticed ctx) ctx))))
    (testing "the firing rests on the edge it travelled"
      (v/retract! kb (v/handle-of kb (list 'genlCx CxNarrow CxWide) ctx))
      (is (not (holds? kb (list noticed CxNarrow)))
          "retracting the lattice edge withdraws the conclusion")
      (v/assert kb (list 'genlCx CxNarrow CxWide) ctx)
      (is (holds? kb (list noticed CxNarrow))
          "and the edge arriving last reconnects and re-fires it"))))

(tu/deftest-kb a-defeated-witness-with-a-surviving-route-keeps-the-entry-points-agreeing
  ;; `supports-for` names one witness per reader, and arbitration can defeat that witness with no
  ;; sentence arriving or leaving: the denial lands where it sees nothing, and a lattice
  ;; edge arriving later exposes the pair.  The firing has to re-derive through the route
  ;; the named witness did not travel, in the very settle that defeated it, or the
  ;; fixpoint holds less than the backward entry point still proves.
  ;;
  ;;   CxUniverse   (transitiveInArg largerThan 1 genl)  (largerThan dog_t cat_t)
  ;;    ├─ CxA      (genl chi_t mid_t) (genl mid_t dog_t)   the long route
  ;;    │           (genl chi_t dog_t)                      the short route, the witness
  ;;    └─ CxB      (not (genl chi_t dog_t))  monotonic
  ;;
  ;; Both routes are stated in CxA, so they place the conclusion in the same context and
  ;; the shorter one is the witness (`taxonomy/general-reach-supports`).
  (tu/with-terms [dog_t mid_t chi_t cat_t largerThan noted CxA CxB]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl mid_t dog_t) CxA)
      (v/assert kb (list 'genl chi_t mid_t) CxA)
      (v/assert kb (list 'genl chi_t dog_t) CxA)
      (v/assert kb (list 'transitiveInArg largerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list largerThan dog_t cat_t) 'CxUniverse))
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list noted '?x '?y))
              'CxUniverse {:direction :forward})
    (let [goal (list noted chi_t cat_t)]
      (is (seq (v/sentexes-matching kb goal CxA))
          "the firing lands beside the edges it named")
      (testing "the denial lands where it sees nothing, and nothing moves"
        (v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB {:strength :monotonic})
        (is (seq (v/sentexes-matching kb goal CxA))))
      (testing "the lattice edge exposes the pair, and the firing re-derives on the
                surviving route in the settle that defeated its witness"
        ;; The edge makes CxA see the denial, so CxA — the witness's own context — is the
        ;; vantage and the defeat reaches every reader of the witness.  An edge the other
        ;; way would make CxB the vantage, and the witness would stay believed in CxA
        ;; (docs/nmtms.md, "A defeat is scoped to its vantage").
        (v/assert kb (list 'genlCx CxA CxB) 'CxUniverse)
        (is (v/ask? kb (list largerThan chi_t cat_t) CxA)
            "the backward entry point still proves the claim through the long route")
        (is (seq (v/sentexes-matching kb goal CxA))
            "and the fixpoint holds it again, on the route that survived")
        (is (v/ask? kb goal CxA) "both entry points agree with the prover")))))

(tu/deftest-kb the-witness-is-the-route-that-places-the-conclusion-highest
  ;; A reachability with two routes carries one witness, and which one it is decides where
  ;; the conclusion lives.  The route through the general context is taken even where it is
  ;; longer, so the firing is placed above both routes' specific contexts and every reader
  ;; of either route holds it (docs/contexts.md, "The consumers, and what each of them may
  ;; reach").
  ;;
  ;;   CxUniverse   (genl mid_t dog_t) (genl chi_t mid_t)   the long route
  ;;                (transitiveInArg largerThan 1 genl)  (largerThan dog_t cat_t)
  ;;    └─ CxA      (genl chi_t dog_t)                      the short route
  ;;         └─ CxB (not (genl chi_t dog_t))  monotonic
  (doseq [long-first? [true false]]
    (testing (if long-first? "the long route arrives first" "the short route arrives first")
      (tu/with-terms [dog_t mid_t chi_t cat_t largerThan noted CxA CxB]
        (let [long! #(do (v/assert kb (list 'genl mid_t dog_t) 'CxUniverse)
                         (v/assert kb (list 'genl chi_t mid_t) 'CxUniverse))
              short! #(v/assert kb (list 'genl chi_t dog_t) CxA)
              goal   (list noted chi_t cat_t)]
          (v/with-deferred-settle kb
            (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
            (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
            (v/assert kb (list 'transitiveInArg largerThan 1 'genl) 'CxUniverse)
            (v/assert kb (list largerThan dog_t cat_t) 'CxUniverse)
            (v/assert kb (list 'implies (list largerThan '?x '?y) (list noted '?x '?y))
                      'CxUniverse {:direction :forward}))
          (if long-first? (do (long!) (short!)) (do (short!) (long!)))
          (testing "the conclusion is placed where the long route is visible"
            (is (seq (v/sentexes-matching kb goal 'CxUniverse))))
          (testing "and rests on the long route's two edges, not on the short one"
            (let [reasons (into #{}
                                (comp (mapcat :because) (map :sentence))
                                (:support (v/why kb (v/handle-of kb goal 'CxUniverse))))]
              (is (contains? reasons (list 'genl mid_t dog_t)))
              (is (contains? reasons (list 'genl chi_t mid_t)))
              (is (not (contains? reasons (list 'genl chi_t dog_t))))))
          (testing "and every reader holds it, in either arrival order"
            (is (v/ask? kb goal 'CxUniverse))
            (is (v/ask? kb goal CxA))
            (is (v/ask? kb goal CxB)))
          (testing "a clash below the general context moves no reader's answer"
            (v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB {:strength :monotonic})
            (is (v/ask? kb goal 'CxUniverse))
            (is (v/ask? kb goal CxA))
            (is (v/ask? kb goal CxB) "CxB sees the long route and reads the conclusion"))
          (testing "and retracting it moves no reader's answer back"
            (v/retract! kb (v/handle-of kb (list 'not (list 'genl chi_t dog_t)) CxB))
            (is (v/ask? kb goal 'CxUniverse))
            (is (v/ask? kb goal CxA))
            (is (v/ask? kb goal CxB))))))))

(defn- two-route-lattice!
  "The lattice above without the clash: the long route `chi → mid → dog` in CxUniverse,
  the short route `chi → dog` in CxA, CxB below CxA.  `routes` names which of the two are
  asserted, in that order."
  [kb {:keys [dog_t mid_t chi_t cat_t largerThan noted CxA CxB]} routes]
  (v/with-deferred-settle kb
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
    (v/assert kb (list 'transitiveInArg largerThan 1 'genl) 'CxUniverse)
    (v/assert kb (list largerThan dog_t cat_t) 'CxUniverse)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list noted '?x '?y))
              'CxUniverse {:direction :forward}))
  (doseq [r routes]
    (case r
      :long  (do (v/assert kb (list 'genl mid_t dog_t) 'CxUniverse)
                 (v/assert kb (list 'genl chi_t mid_t) 'CxUniverse))
      :short (v/assert kb (list 'genl chi_t dog_t) CxA))))

(defn- two-route-reading
  "Where `(noted chi cat)` is stored, and what CxUniverse, CxA and CxB each answer."
  [kb {:keys [chi_t cat_t noted CxA CxB]}]
  (let [goal    (list noted chi_t cat_t)
        readers ['CxUniverse CxA CxB]]
    {:stored  (mapv #(some? (v/handle-of kb goal %)) readers)
     :answers (mapv #(v/ask? kb goal %) readers)}))

(tu/deftest-kb retracting-either-route-leaves-what-a-kb-built-without-it-holds
  ;; The short route first stores the firing twice — once over the short route in CxA, and
  ;; again in CxUniverse when the long route arrives — and the long route first stores it
  ;; once.  Retracting either route from either order leaves the store and every reader's
  ;; answer that a KB built with only the other route holds.
  (doseq [order    [[:long :short] [:short :long]]
          retracted [:long :short]]
    (testing (str (name (first order)) " route first, the " (name retracted) " route retracted")
      (let [kept (first (remove #{retracted} order))
            terms (fn [] (zipmap [:dog_t :mid_t :chi_t :cat_t :largerThan :noted :CxA :CxB]
                                 (map #(tu/fresh-term (tu/term-role %) %)
                                      '[dog_t mid_t chi_t cat_t largerThan noted CxA CxB])))
            built (terms)
            alone (terms)]
        (two-route-lattice! kb built order)
        (let [{:keys [dog_t mid_t chi_t CxA]} built]
          (doseq [[s c] (if (= :long retracted)
                          [[(list 'genl mid_t dog_t) 'CxUniverse]
                           [(list 'genl chi_t mid_t) 'CxUniverse]]
                          [[(list 'genl chi_t dog_t) CxA]])]
            (v/retract! kb (v/handle-of kb s c))))
        (two-route-lattice! kb alone [kept])
        (is (= (two-route-reading kb alone) (two-route-reading kb built)))))))

(tu/deftest-kb a-reader-that-loses-the-long-route-reads-the-conclusion-in-either-order
  ;; A scoped defeat of the long route at CxA withdraws the CxUniverse firing there, while
  ;; CxA still reaches chi → dog over its own edge.  The short route first stored a firing
  ;; in CxA before the long route arrived; the long route first stored none, and the settle
  ;; re-derives one over CxA's route (settle/lost-firing-seeds).  Either way CxA holds a
  ;; firing of its own afterwards, and it is kept rather than retired (docs/defenses.md, "A
  ;; firing placed over a lower route is not retired").
  (doseq [order [[:short :long] [:long :short]]]
    (testing (str (name (first order)) " route first")
      (tu/with-terms [dog_t mid_t chi_t cat_t largerThan noted CxA CxB]
        (let [t {:dog_t dog_t :mid_t mid_t :chi_t chi_t :cat_t cat_t :largerThan largerThan
                 :noted noted :CxA CxA :CxB CxB}]
          (two-route-lattice! kb t order)
          (v/assert kb (list 'not (list 'genl chi_t mid_t)) CxA {:strength :monotonic})
          (is (= [true true true] (:answers (two-route-reading kb t)))
              "CxA reaches chi → dog over its own edge and reads the conclusion")
          (is (= [true true false] (:stored (two-route-reading kb t)))
              "stored in CxUniverse and in CxA"))))))

(tu/deftest-kb the-mirror-licenses-a-firing-in-either-order
  ;; A symmetric predicate's stored claim states both orientations, so the mirror
  ;; orientation licenses inheritance like the stored one — through the forward entry point as
  ;; much as the backward, whichever of the claim and the symmetry arrived first.  The
  ;; firing names the symmetric declaration it was read through, so withdrawing the
  ;; symmetry withdraws exactly what only the mirror licensed.
  (doseq [sym-first? [true false]]
    (testing (if sym-first? "the symmetry arrives before the claim" "the symmetry arrives last")
      (tu/with-terms [dog_t cat_t chihuahua_t nearTo seen]
        (v/with-deferred-settle kb
          (v/assert kb (list 'genl chihuahua_t dog_t) ctx)
          (v/assert kb (list 'transitiveInArg nearTo 1 'genl) ctx))
        (doseq [s (if sym-first?
                    [(list 'symmetric nearTo)
                     (list 'set/forwardRule (list 'implies (list nearTo '?x '?y) (list seen '?x '?y)))
                     (list nearTo cat_t dog_t)]
                    [(list nearTo cat_t dog_t)
                     (list 'set/forwardRule (list 'implies (list nearTo '?x '?y) (list seen '?x '?y)))
                     (list 'symmetric nearTo)])]
          (v/assert kb s ctx))
        (testing "the tuple only the mirror licenses, through both entry points"
          (is (v/ask? kb (list nearTo chihuahua_t cat_t) ctx))
          (is (holds? kb (list seen chihuahua_t cat_t)))
          (is (v/ask? kb (list seen chihuahua_t cat_t) ctx)))
        (testing "the firing names the symmetry it was read through"
          (let [reasons (into #{}
                              (comp (mapcat :because) (map :sentence))
                              (:support (v/why kb (v/handle-of kb (list seen chihuahua_t cat_t)
                                                               ctx))))]
            (is (contains? reasons (list 'symmetric nearTo)))
            (is (contains? reasons (list nearTo cat_t dog_t)))))
        (testing "withdrawing the symmetry withdraws what only the mirror licensed"
          (v/retract! kb (v/handle-of kb (list 'symmetric nearTo) ctx))
          (is (not (holds? kb (list seen chihuahua_t cat_t))))
          (is (not (v/ask? kb (list nearTo chihuahua_t cat_t) ctx)))
          (is (holds? kb (list seen cat_t dog_t)) "the stated orientation is untouched")
          (v/assert kb (list 'symmetric nearTo) ctx)
          (is (holds? kb (list seen chihuahua_t cat_t)) "and re-asserting restores it"))))))

(tu/deftest-kb a-defeated-reason-withdraws-the-firing-and-revival-restores-it
  ;; The JTMS half of `retracting-any-reason-withdraws-the-conclusion`: belief loss
  ;; without retraction.  Each reason in turn is defeated by a known-true contrary and
  ;; revived by that contrary's retraction, and the firing follows it out and back
  ;; through both entry points.
  (tu/with-terms [dog_t cat_t chihuahua_t maine_coon_t largerThan outweighs]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl chihuahua_t dog_t) ctx)
      (v/assert kb (list 'genl maine_coon_t cat_t) ctx)
      (v/assert kb (list 'transitiveInArg largerThan 1 'genl) ctx)
      (v/assert kb (list 'transitiveInArg largerThan 2 'genl) ctx)
      (v/assert kb (list largerThan dog_t cat_t) ctx))
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx {:direction :forward})
    (let [goal (list outweighs chihuahua_t maine_coon_t)]
      (is (holds? kb goal))
      (doseq [reason [(list 'genl chihuahua_t dog_t)
                      (list largerThan dog_t cat_t)]]
        (testing (str "defeating " (pr-str reason))
          (v/assert kb (list 'not reason) ctx {:strength :monotonic})
          (is (not (holds? kb goal)) "the defeated reason takes the firing out")
          (is (not (v/ask? kb goal ctx)))
          (v/retract! kb (v/handle-of kb (list 'not reason) ctx))
          (is (holds? kb goal) "and the revival re-derives it")
          (is (v/ask? kb goal ctx)))))))

(tu/deftest-kb an-R-fact-arriving-last-connects-and-fires
  ;; genl has the shuffled oracle and genlCx the relanding edge; this is the
  ;; declared relation's turn: the trigger index cannot connect `partOf` to the
  ;; preserved predicate, so only the preserving re-join fires these.
  (tu/with-terms [partOf needs_maintenance schedule Car Engine Piston]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive partOf) ctx)
      (v/assert kb (list 'transitiveInArg needs_maintenance 1 partOf) ctx))
    (v/assert kb (list needs_maintenance Car) ctx)
    (v/assert kb (list 'implies (list needs_maintenance '?x) (list schedule '?x)) ctx {:direction :forward})
    (is (not (holds? kb (list schedule Piston))) "nothing connects the part yet")
    (v/assert kb (list partOf Engine Car) ctx)
    (is (holds? kb (list schedule Engine)) "one hop, connected by the late fact")
    (v/assert kb (list partOf Piston Engine) ctx)
    (is (holds? kb (list schedule Piston)) "and the second hop extends the reach")
    (testing "withdrawing and re-asserting the transitivity round-trips the firings"
      (v/retract! kb (v/handle-of kb (list 'transitive partOf) ctx))
      (is (not (holds? kb (list schedule Piston))))
      (v/assert kb (list 'transitive partOf) ctx)
      (is (holds? kb (list schedule Piston))))))

(tu/deftest-kb a-batch-and-a-sequence-reach-the-same-firings-off-genl
  ;; One `with-deferred-settle` batch and the same content asserted one at a time
  ;; must land the same conclusions, for the declared relation and the lattice alike —
  ;; the batch's closing fixpoint interleaves the re-joins the sequence took one per
  ;; arrival.
  (doseq [batch? [true false]]
    (testing (if batch? "one deferred batch" "one assert at a time")
      (tu/with-terms [partOf needs_maintenance schedule Car Engine Piston
                      appliesIn noticed TheDecree CxWide CxNarrow]
        (let [content [(list 'transitive partOf)
                       (list 'transitiveInArg needs_maintenance 1 partOf)
                       (list partOf Engine Car)
                       (list partOf Piston Engine)
                       (list needs_maintenance Car)
                       (list 'set/forwardRule (list 'implies (list needs_maintenance '?x) (list schedule '?x)))
                       (list 'genlCx CxWide ctx)
                       (list 'genlCx CxNarrow CxWide)
                       (list 'transitiveInArg appliesIn 2 'genlCx)
                       (list appliesIn TheDecree CxWide)
                       (list 'set/forwardRule (list 'implies (list appliesIn TheDecree '?c) (list noticed '?c)))]]
          (if batch?
            (v/with-deferred-settle kb
              (doseq [s content] (v/assert kb s ctx)))
            (doseq [s content] (v/assert kb s ctx))))
        (is (holds? kb (list schedule Piston)) "the part chain fired")
        (is (holds? kb (list schedule Engine)))
        (is (holds? kb (list noticed CxNarrow)) "and the lattice fired")
        (is (not (holds? kb (list noticed ctx))))))))

(tu/deftest-kb a-genlCx-carried-firing-descends-to-where-the-lattice-is-visible
  ;; Placement for the lattice relation: the claim in one branch, the edge in another,
  ;; and the conclusion lands only where both are visible — the context below the two.
  (tu/with-terms [appliesIn noticed TheDecree CxWide CxNarrow
                  CxLeft CxRight CxDown]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlCx CxLeft ctx) ctx)
      (v/assert kb (list 'genlCx CxRight ctx) ctx)
      (v/assert kb (list 'genlCx CxDown CxLeft) ctx)
      (v/assert kb (list 'genlCx CxDown CxRight) ctx)
      (v/assert kb (list 'genlCx CxWide ctx) ctx)
      (v/assert kb (list 'genlCx CxNarrow CxWide) ctx)
      (v/assert kb (list 'transitiveInArg appliesIn 2 'genlCx) ctx))
    (v/assert kb (list appliesIn TheDecree CxWide) CxLeft)
    (v/assert kb (list 'implies (list appliesIn TheDecree '?c) (list noticed '?c))
              CxRight {:direction :forward})
    (is (seq (v/sentexes-matching kb (list noticed CxNarrow) CxDown))
        "the conclusion is homed below both branches")
    (is (empty? (v/sentexes-matching kb (list noticed CxNarrow) CxLeft))
        "and not in a branch that cannot see the rule")
    (is (v/ask? kb (list noticed CxNarrow) CxDown))))

;; ---- joining with an ordinary antecedent --------------------------------

(tu/deftest-kb an-inherited-antecedent-joins-with-a-matched-one
  ;; The other shape: the ordinary antecedent binds the variables first, so the
  ;; preserved one reaches the join closed and asks one question per binding.  The
  ;; rule goes in **first** here, so the join runs at the arriving fact's trigger
  ;; position rather than as the rule's own full pass.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan competing winsAgainst]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list 'and (list competing '?x '?y) (list largerThan '?x '?y))
                       (list winsAgainst '?x '?y))
              ctx {:direction :forward})
    (v/assert kb (list competing chihuahua_t maine_coon_t) ctx)
    (v/assert kb (list competing maine_coon_t chihuahua_t) ctx)
    (is (holds? kb (list winsAgainst chihuahua_t maine_coon_t)))
    (is (not (holds? kb (list winsAgainst maine_coon_t chihuahua_t)))
        "the other direction is not licensed, so the join finds nothing")))

(tu/deftest-kb a-derived-claim-licenses-the-inheritance-a-stated-one-does
  ;; A claim the fixpoint concluded is a datum like any other, so it re-joins the rules
  ;; over its predicate — or which claims inherit would depend on whether somebody
  ;; wrote them or a rule reached them.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs bulkierThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list 'implies (list bulkierThan '?x '?y) (list largerThan '?x '?y)) ctx {:direction :forward})
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx {:direction :forward})
    (v/assert kb (list bulkierThan dog_t cat_t) ctx)
    (is (holds? kb (list largerThan dog_t cat_t)) "the first rule concluded the claim")
    (is (holds? kb (list outweighs chihuahua_t maine_coon_t))
        "and the second fired on what that claim licenses")))

;; ---- placement ----------------------------------------------------------

(tu/deftest-kb the-conclusion-lands-where-its-reasons-can-be-seen
  (tu/with-terms [dog_t cat_t chihuahua_t maine_coon_t largerThan outweighs
                  CxUpper CxLower]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlCx CxUpper ctx) ctx)
      (v/assert kb (list 'genlCx CxLower CxUpper) ctx))
    (v/with-deferred-settle kb
      (v/assert kb (list 'asymmetric largerThan) CxUpper)
      (v/assert kb (list 'transitiveInArg largerThan 1 'genl) CxUpper)
      (v/assert kb (list 'transitiveInArg largerThan 2 'genl) CxUpper)
      (v/assert kb (list largerThan dog_t cat_t) CxUpper))
    ;; the edges are stated only in the lower context, so only it can see the reach
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl chihuahua_t dog_t) CxLower)
      (v/assert kb (list 'genl maine_coon_t cat_t) CxLower))
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y))
              CxUpper {:direction :forward})
    (let [[sx & more] (v/sentexes-matching kb (list outweighs chihuahua_t maine_coon_t)
                                           CxLower)]
      (is (nil? more) "one placement, so reading it names no order")
      (is (some? sx) "derived, from the one context that sees the rule, the claim and both edges")
      (is (= CxLower (:context sx))
          "and it descends to the edges rather than sitting above them"))
    (is (empty? (v/sentexes-matching kb (list outweighs chihuahua_t maine_coon_t) CxUpper))
        "the context that cannot see the edges does not hold the conclusion")))

(tu/deftest-kb a-firing-with-no-common-context-is-reported-rather-than-dropped
  (tu/with-terms [dog_t cat_t chihuahua_t maine_coon_t largerThan outweighs
                  CxBase CxLeft CxRight]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlCx CxBase ctx) ctx)
      (v/assert kb (list 'genlCx CxLeft CxBase) ctx)
      (v/assert kb (list 'genlCx CxRight CxBase) ctx))
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitiveInArg largerThan 1 'genl) CxBase)
      (v/assert kb (list 'transitiveInArg largerThan 2 'genl) CxBase)
      (v/assert kb (list largerThan dog_t cat_t) CxBase))
    ;; incomparable contexts hold one edge each: no context sees both
    (v/assert kb (list 'genl chihuahua_t dog_t) CxLeft)
    (v/assert kb (list 'genl maine_coon_t cat_t) CxRight)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y))
              CxBase {:direction :forward})
    (is (empty? (v/sentexes-matching kb (list outweighs chihuahua_t maine_coon_t) CxLeft)))
    (is (empty? (v/sentexes-matching kb (list outweighs chihuahua_t maine_coon_t) CxRight)))
    (is (some #(and (= :no-placement (:violation %))
                    (= (list outweighs chihuahua_t maine_coon_t) (:sentence %)))
              (v/violations kb))
        "a completed firing that lands nowhere is recorded, never silently dropped")))

;; ---- a KB that declares nothing ----------------------------------------

(tu/deftest-kb no-declaration-derives-nothing-new
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx {:direction :forward})
    (is (= [(list outweighs dog_t cat_t)]
           (mapv :sentence (v/sentexes-matching kb (list outweighs '?x '?y) ctx)))
        "the stored claim's own tuple and nothing else")))

;; ---- order independence -------------------------------------------------

(defn- derived-outweighs
  "The derived content and the justifications behind it, by **content** — handles are
  allocated in assertion order, which is the one thing a reordering must not move."
  [kb pred]
  (let [sentences (into #{} (map :sentence) (v/sentexes-matching kb (list pred '?x '?y) ctx))]
    {:derived sentences
     :because (into #{}
                    (map (fn [s]
                           [s (into #{}
                                    (comp (mapcat :because) (map :sentence))
                                    (:support (v/why kb (v/handle-of kb s ctx))))]))
                    sentences)}))

(defn- shuffled
  "A permutation of `xs` from `rng` — `clojure.core/shuffle` reads a global source, and
  a randomized oracle that cannot be replayed from its seed is not one."
  [xs ^java.util.Random rng]
  (let [a (java.util.ArrayList. ^java.util.Collection (vec xs))]
    (java.util.Collections/shuffle a rng)
    (vec a)))

(tu/deftest-kb the-same-content-in-any-order-reaches-the-same-firings
  ;; Every failure on this path is a *missing* answer — a firing the trigger index
  ;; could not connect — and a KB that is merely less informative than it should be
  ;; reads as correct against anything except another order of the same content.  So
  ;; the declaration, the edges, the claim and the rule are permuted together: "the
  ;; rule arrived last" is what a rule's own full join would otherwise paper over.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (let [content [(list 'genl chihuahua_t dog_t)
                   (list 'genl golden_retriever_t dog_t)
                   (list 'genl maine_coon_t cat_t)
                   (list 'genl siamese_t cat_t)
                   (list 'transitiveInArg largerThan 1 'genl)
                   (list 'transitiveInArg largerThan 2 'genl)
                   (list largerThan dog_t cat_t)
                   (list 'set/forwardRule (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)))]
          go   (fn [order]
                 (let [k (tu/isolated-fresh)]
                   (try
                     (doseq [s order] (v/assert k s ctx))
                     (derived-outweighs k outweighs)
                     (finally (tu/clear-kb! k)))))
          rng  (java.util.Random. 20260804)
          runs (mapv (fn [_] (go (shuffled content rng))) (range 8))]
      (is (= 9 (count (:derived (first runs)))) "the run is not vacuous")
      (doseq [[i r] (map-indexed vector (rest runs))]
        (is (= (first runs) r)
            (str "order " (inc i) " reached a different fixpoint:\n"
                 (pr-str (set/difference (:derived (first runs)) (:derived r)))
                 " / "
                 (pr-str (set/difference (:derived r) (:derived (first runs))))))))))
