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
            [vaelii.test-util :as tu]))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'implies (cons 'and antes) conseq)))

(defn- run-ops
  "Apply `ops` to a freshly cleared KB and return `observe`'s reading of it."
  [ops observe]
  (let [kb (tu/fresh)]
    (doseq [op ops] (op kb))
    (observe kb)))

(defn- outcomes
  "The set of distinct outcomes over every ordering of `ops`."
  [ops observe]
  (into #{} (map #(run-ops % observe)) (permutations ops)))

(defn- one-outcome!
  "Assert that every ordering of `ops` agrees, and return the single outcome."
  [label ops observe]
  (let [os (outcomes ops observe)]
    (is (= 1 (count os))
        (str label ": " (count os) " distinct outcomes across "
             (count (permutations ops)) " orderings — " (pr-str os)))
    (first os)))

;; ---- defaults and their exceptions --------------------------------------

(deftest penguin-cascade-is-order-independent
  ;; 5 assertions, 120 orderings. The default may fire before or after the KB learns
  ;; Tweety is a penguin, before or after it learns penguins are birds at all.
  (let [ops [#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'UniverseContext)
             #(v/assert-rule % '[(penguin ?x)] '(not (flies ?x)) 'UniverseContext)
             #(v/assert % '(genl penguin bird) 'UniverseContext)
             ;; Known-true: a bare rule confers :monotonic and is capped by its weakest
             ;; antecedent, so over this premise the exception concludes :monotonic and
             ;; out-ranks the :default flight rule.  Over a :default premise both sides
             ;; would tie at :default and the pair would be a represented dilemma.
             #(v/assert % '(penguin Tweety) 'UniverseContext {:strength :monotonic})
             #(v/assert % '(bird Robin) 'UniverseContext)]
        observe (fn [kb]
                  {:tweety-flies (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'UniverseContext)))
                   :tweety-grounded (boolean (seq (v/sentexes-matching kb '(not (flies Tweety)) 'UniverseContext)))
                   :robin-flies (boolean (seq (v/sentexes-matching kb '(flies Robin) 'UniverseContext)))
                   :conflicts (count (v/conflicts kb))})
        result (one-outcome! "penguin cascade" ops observe)]
    (testing "and the one outcome is the common-sense one"
      (is (false? (:tweety-flies result)))
      (is (true? (:tweety-grounded result)))
      (is (true? (:robin-flies result)))                ; the exception is not contagious
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest exceptwhen-is-order-independent
  ;; The exception is a belief-following meta-sentex split off from the rule, so the
  ;; exceptWhen may arrive before its facts (blocking the firing at derive time) or
  ;; after them (sweeping a conclusion that already fired).  Both must settle to the
  ;; same belief, forward *and* backward — the whole point of the block/sweep machinery
  ;; being order-independent.  24 orderings.
  (let [ops [#(v/assert % '(exceptWhen (penguin ?x)
                                       (set/defaultRule (implies (and (bird ?x)) (flies ?x))))
                        'UniverseContext)
             #(v/assert % '(penguin Tweety) 'UniverseContext)
             #(v/assert % '(bird Tweety) 'UniverseContext)
             #(v/assert % '(bird Robin) 'UniverseContext)]
        observe (fn [kb]
                  {:tweety-query (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'UniverseContext)))
                   :tweety-ask   (v/ask? kb '(flies Tweety) 'UniverseContext)
                   :robin-query  (boolean (seq (v/sentexes-matching kb '(flies Robin) 'UniverseContext)))
                   :conflicts    (count (v/conflicts kb))})
        result (one-outcome! "exceptWhen" ops observe)]
    (testing "the excepted binding never flies, forward or backward; the other does"
      (is (false? (:tweety-query result)))
      (is (false? (:tweety-ask result)))
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
                                             (set/defaultRule (implies (and (bird ?x)) (flies ?x))))
                             'UniverseContext)
              :r2 #(v/assert kb '(exceptWhen (ostrich ?x)
                                             (set/defaultRule (implies (and (bird ?x)) (flies ?x))))
                             'UniverseContext)
              :fp #(v/assert kb '(bird Pengu) 'UniverseContext)
              :tp #(v/assert kb '(penguin Pengu) 'UniverseContext)
              :fo #(v/assert kb '(bird Ostri) 'UniverseContext)
              :to #(v/assert kb '(ostrich Ostri) 'UniverseContext)
              :fr #(v/assert kb '(bird Robby) 'UniverseContext)}]
      (doseq [k order] ((op k)))
      (is (empty? (v/sentexes-matching kb '(flies Pengu) 'UniverseContext)) (str order " penguin flies"))
      (is (empty? (v/sentexes-matching kb '(flies Ostri) 'UniverseContext)) (str order " ostrich flies"))
      (is (seq (v/sentexes-matching kb '(flies Robby) 'UniverseContext)) (str order " robin grounded"))
      (tu/clear-kb! kb))))

(deftest a-default-feeding-a-bare-rule-is-order-independent
  ;; The downstream conclusion (canTravel) must track the defeat of its antecedent
  ;; whichever order the pieces arrive in.
  (let [ops [#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'UniverseContext)
             #(v/assert-rule % '[(flies ?x)] '(canTravel ?x) 'UniverseContext)
             #(v/assert-rule % '[(penguin ?x)] '(not (flies ?x)) 'UniverseContext)
             #(v/assert % '(genl penguin bird) 'UniverseContext)
             ;; known-true, so the exception concludes :monotonic and defeats the default
             #(v/assert % '(penguin Tweety) 'UniverseContext {:strength :monotonic})]
        observe (fn [kb]
                  {:flies (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'UniverseContext)))
                   :travels (boolean (seq (v/sentexes-matching kb '(canTravel Tweety) 'UniverseContext)))})
        result (one-outcome! "default feeding a bare rule" ops observe)]
    (testing "a defeated antecedent withdraws the conclusion built on it"
      (is (false? (:flies result)))
      (is (false? (:travels result))))
    (tu/clear-kb! (tu/test-kb))))

;; ---- the represented dilemma --------------------------------------------

(deftest nixon-diamond-is-the-same-dilemma-every-time
  ;; Two equally-specific defaults collide with no strength and no specificity to
  ;; separate them, and neither rule names the other's case. The engine declines to
  ;; decide that: both sides stay believed and the pair is reported by
  ;; `contradictions`. What must not vary with typing order is the whole reading —
  ;; which sides are believed, that neither was defeated, and that exactly one dilemma
  ;; is reported.
  (let [ops [#(v/assert % (default-rule '[(quaker ?x)] '(pacifist ?x)) 'UniverseContext)
             #(v/assert % (default-rule '[(republican ?x)] '(not (pacifist ?x))) 'UniverseContext)
             #(v/assert % '(quaker Nixon) 'UniverseContext)
             #(v/assert % '(republican Nixon) 'UniverseContext)]
        observe (fn [kb]
                  (let [pos (v/handle-of kb '(pacifist Nixon) 'UniverseContext)
                        neg (v/handle-of kb '(not (pacifist Nixon)) 'UniverseContext)]
                    {:pacifist (boolean (seq (v/sentexes-matching kb '(pacifist Nixon) 'UniverseContext)))
                     :not-pacifist (boolean (seq (v/sentexes-matching kb '(not (pacifist Nixon)) 'UniverseContext)))
                     ;; the defeat-classes, not the handles: handles are allocated in
                     ;; assertion order, so putting one in the reading would make every
                     ;; ordering differ for a reason that is not about belief.  Keyed
                     ;; positive-then-negative, so a defeated or missing side reads as
                     ;; nil in its own slot rather than vanishing into a set.
                     :classes [(v/defeat-class kb pos) (v/defeat-class kb neg)]
                     :contradictions (count (v/contradictions kb))
                     :conflicts (count (v/conflicts kb))}))
        result (one-outcome! "nixon diamond" ops observe)]
    (testing "both sides are believed — the dilemma is represented, not decided"
      (is (true? (:pacifist result)))
      (is (true? (:not-pacifist result))))
    (testing "and neither was defeated — both still stand at :default"
      (is (= [:default :default] (:classes result))))
    (testing "the pair is reported once as a dilemma, not as a conflict"
      (is (= 1 (:contradictions result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

;; ---- retraction and revival ---------------------------------------------

(deftest revival-is-order-independent
  ;; Build the default in either order, defeat it, then retract the defeater. The
  ;; conclusion must come back in both cases — belief is recomputed, not replayed.
  (doseq [build [[#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'UniverseContext)
                  #(v/assert % '(bird Sky) 'UniverseContext)]
                 [#(v/assert % '(bird Sky) 'UniverseContext)
                  #(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'UniverseContext)]]]
    (let [kb (tu/fresh)]
      (doseq [op build] (op kb))
      (is (seq (v/sentexes-matching kb '(flies Sky) 'UniverseContext)) "the default holds")
      (let [neg (v/assert kb '(not (flies Sky)) 'UniverseContext {:strength :monotonic})]
        (is (empty? (v/sentexes-matching kb '(flies Sky) 'UniverseContext)) "defeated")
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb '(flies Sky) 'UniverseContext)) "revived"))))
  (tu/clear-kb! (tu/test-kb)))

;; ---- the taxonomy caches follow suit ------------------------------------

(deftest genl-closure-is-order-independent
  ;; The cached closures are derived state, so they must land in the same place
  ;; whatever order the edges and their defeater arrive in.
  (let [ops [#(v/assert % '(genl sub_t mid_t) 'UniverseContext)
             #(v/assert % '(genl mid_t super_t) 'UniverseContext)
             #(v/assert % '(sub_t Ind1) 'UniverseContext)]
        observe (fn [kb] {:isa (v/isa? kb 'Ind1 'super_t)})]
    (is (= #{{:isa true}} (outcomes ops observe))
        "transitive membership does not depend on which edge was asserted first"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-firing-that-subsumes-is-order-independent
  ;; The closure landing in the same place is not enough: matching fans an antecedent
  ;; over its spec closure, so a `genl` edge changes which antecedents the *stored*
  ;; facts satisfy.  The arriving datum is the edge, and firing the rules keyed on
  ;; `genl` is not the same thing as re-firing the rules the edge just connected — so
  ;; without `special/subsumption-seeds` these four sentences derive `(breathes Muffet)`
  ;; in the orders that put the edge before the fact and nothing in the others.
  (let [ops [#(v/assert % '(genl animal_t thing) 'UniverseContext)
             #(v/assert % '(genl dog_t animal_t) 'UniverseContext)
             #(v/assert % '(implies (animal_t ?x) (breathes ?x)) 'UniverseContext)
             #(v/assert % '(dog_t Muffet) 'UniverseContext)]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(breathes Muffet) 'UniverseContext)))})]
    (is (= {:derived true} (one-outcome! "subsumption firing" ops observe))
        "and the one outcome is the conclusion, not the silence"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-firing-that-sees-across-a-context-edge-is-order-independent
  ;; The same claim for the other closure, and the same gap.  Matching fans an
  ;; antecedent up the *visibility* cone, so a `genlContext` edge changes which facts a
  ;; stored rule can see — and the arriving datum is again the edge, so firing the rules
  ;; keyed on `genlContext` is not the same thing as re-joining the rules the edge just
  ;; gave a wider view.  Without `special/visibility-seeds` these four sentences derive
  ;; `(vSeenP VA)` in the 17 orders that put the edge before the rule or the fact, and
  ;; nothing in the other 7.
  (let [ops [#(v/assert % '(genlContext VMidContext UniverseContext) 'UniverseContext)
             #(v/assert % '(genlContext VLowContext VMidContext) 'UniverseContext)
             #(v/assert % '(vFactP VA) 'VMidContext)
             #(v/assert % '(implies (vFactP ?x) (vSeenP ?x)) 'VLowContext)]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(vSeenP VA) 'VLowContext)))})]
    (is (= {:derived true} (one-outcome! "visibility firing" ops observe))
        "a rule fires off what its context can see, whenever it was told it could"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-rule-above-fires-on-the-facts-of-a-context-newly-wired-under-it
  ;; the other direction of the same edge, and the one that survives a fix taking only
  ;; the first: a rule stated *above* applies in every context that sees it, so wiring a
  ;; new context under it hands the rule that context's own facts and places
  ;; the conclusion there.  Seeding is by fact, so it has to reach both cones.
  (let [ops [#(v/assert % '(genlContext XMidContext UniverseContext) 'UniverseContext)
             #(v/assert % '(genlContext XLowContext XMidContext) 'UniverseContext)
             #(v/assert % '(xFactP XB) 'XLowContext)
             #(v/assert % '(implies (xFactP ?x) (xSeenP ?x)) 'XMidContext)]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(xSeenP XB) 'XLowContext)))})]
    (is (= {:derived true} (one-outcome! "inherited-rule firing" ops observe))
        "a rule above is inherited into a context wired under it, whenever that happened"))
  (tu/clear-kb! (tu/test-kb)))

;; The ops are shared by the sampled test and the exhaustive one, so the two cannot
;; drift into checking different things — the only difference between them is how many
;; of the 120 orderings they walk.
(def ^:private derived-edge-ops
  [#(v/assert % '(genlContext WMidContext UniverseContext) 'UniverseContext)
   #(v/assert % '(wFactP WA) 'WMidContext)
   #(v/assert % '(implies (wFactP ?x) (wSeenP ?x)) 'WLowContext)
   #(v/assert % '(wWireP WLowContext WMidContext) 'UniverseContext)
   #(v/assert % '(implies (wWireP ?a ?b) (genlContext ?a ?b)) 'UniverseContext)])

(defn- derived-edge-observe [kb]
  {:derived (boolean (seq (v/sentexes-matching kb '(wSeenP WA) 'WLowContext)))})

(deftest a-derived-context-edge-seeds-like-an-asserted-one
  ;; and a rule concluding the edge reaches the same belief an assert does, or the
  ;; fixpoint would depend on whether the spindle was written or inferred.
  ;;
  ;; Four orderings, not all 120, for the reason `two-independent-exceptions` above
  ;; takes a handful: an ordering here costs ~2s — deriving the edge recomputes the
  ;; genlContext closure and re-places what it reaches, where every other test in this
  ;; file runs an ordering in about a millisecond — so the exhaustive walk is four
  ;; minutes, which is more than the whole rest of the suite.  The handful pins the
  ;; positions that matter: the edge rule first and last, and the fact arriving before
  ;; and after the wiring that has to reach it.  The exhaustive 120 is the `^:slow`
  ;; test below, and `lein gate --all` runs it.
  (doseq [order [[0 1 2 3 4] [4 3 2 1 0] [2 4 3 1 0] [1 3 0 4 2]]]
    (let [ops (mapv derived-edge-ops order)
          kb  (tu/fresh)]
      (doseq [op ops] (op kb))
      (is (= {:derived true} (derived-edge-observe kb))
          (str order ": a derived edge has to seed what an asserted one seeds"))))
  (tu/clear-kb! (tu/test-kb)))

(deftest ^:slow every-ordering-of-a-derived-context-edge-agrees
  ;; The exhaustive form of the test above — all 120 orderings, ~2s apiece.  An
  ;; exhaustive cross-product is what the mark is for, and this is the only test in
  ;; this file that earns it.
  (is (= {:derived true}
         (one-outcome! "derived visibility firing" derived-edge-ops derived-edge-observe))
      "a derived edge has to seed what an asserted one seeds, in any order")
  (tu/clear-kb! (tu/test-kb)))
