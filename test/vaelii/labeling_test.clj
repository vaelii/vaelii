;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.labeling-test
  "The `do/` imperative channel and `(do/labeling Ctx)` (docs/labeling.md).

  Two things are under test and they pull in opposite directions, which is the point.

  **The imperative has to reach the solver.** `settle` builds no `Program` for a
  represented dilemma, so `last-program` is nil exactly where classification is
  interesting; `do/labeling` is the explicit opt-in that builds one from
  `contradictions` and hands it over.

  **And it has to leave the KB alone.** The engine's refusal to arbitrate a dilemma is
  a deliberate stance (docs/exceptions.md), so an imperative that quietly moved belief
  — or that made the same disagreement report twice — would have taken the stance back
  by the side entry point. `belief-unmoved` is checked around every labeling below rather than
  in one test, because that is the property most likely to regress and least likely to
  be noticed.

  Classification itself is exercised in `asp_label_test`; what is new here is the
  channel, the bridge, and the containment."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.label :as label]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- default-rule [ante conseq]
  (list 'set/defaultRule (list 'set/forwardRule (list 'implies ante conseq))))

(defn- dilemma
  "The canonical rebutting dilemma on gensym'd terms — two equally-specific defaults
  concluding `P` and `(not P)` of one individual, neither naming the other's case.
  Returns `{:pred p :individual N :positive h :negative h}`."
  [kb]
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred)
        republican (tu/tmp-pred) nixon (tu/tmp-ind)]
    (v/assert kb (default-rule (list quaker '?x) (list pacifist '?x)) 'CxUniverse)
    (v/assert kb (default-rule (list republican '?x) (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker nixon) 'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    {:pred pacifist
     :individual nixon
     :background (list quaker nixon)          ; uncontested, for inheritance checks
     :positive (v/handle-of kb (list pacifist nixon) 'CxUniverse)
     :negative (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)}))

(defn- belief-snapshot
  "What the base KB believes about a dilemma, and how many it reports."
  [kb {:keys [pred individual]}]
  {:positive (boolean (seq (v/sentexes-matching kb (list pred individual) 'CxUniverse)))
   :negative (boolean (seq (v/sentexes-matching kb (list 'not (list pred individual)) 'CxUniverse)))
   :reported (count (v/contradictions kb))})

;; ---- 1. the do/ channel ------------------------------------------------

(deftest an-imperative-is-never-stored
  ;; The defining property of the channel: `do/` forms are instructions, so no sentex
  ;; exists afterwards and no term index entry points at one.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [ctx (tu/tmp-ctx "Labeling")
          before (count (v/sentexes-in-context kb 'CxUniverse))]
      (v/assert kb (list 'do/labeling ctx) 'CxUniverse)
      (testing "no sentex was stored for the imperative itself"
        (is (nil? (v/handle-of kb (list 'do/labeling ctx) 'CxUniverse)))
        (is (empty? (v/find-sentexes kb 'do/labeling)))
        (is (= before (count (v/sentexes-in-context kb 'CxUniverse))))))))

(deftest an-imperative-is-refused-inside-a-rule
  ;; The one hard constraint. A `do/` form in a rule would run inside the forward
  ;; fixpoint, a number of times that depends on firing order, mutating the KB the
  ;; fixpoint is still computing over — order independence and locality both gone.
  ;; Every slot a rule has is checked, since the guard walks the form rather than
  ;; inspecting three places.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p (tu/tmp-pred) q (tu/tmp-pred) ctx (tu/tmp-ctx "Labeling")
          imp (list 'do/labeling ctx)]
      (doseq [[slot rule]
              [[:consequent (list 'implies (list p '?x) imp)]
               [:antecedent (list 'implies imp (list p '?x))]
               [:exception  (list 'exceptWhen imp
                                  (default-rule (list p '?x) (list q '?x)))]
               [:nested     (list 'implies (list p '?x) (list 'not imp))]]]
        (testing (str "refused in the " (name slot))
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb rule 'CxUniverse)))
          (is (= :not-assertible
                 (try (v/assert kb rule 'CxUniverse) nil
                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))))))

(deftest an-unknown-imperative-names-the-known-ones
  ;; A typo in the `do/` namespace must not read as a fact about a predicate called
  ;; `do/labelling`; it is a caller error and says so.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [e (try (v/assert kb (list 'do/frobnicate 'X) 'CxUniverse) nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= :not-assertible (:type (ex-data e))))
      (is (contains? (:known (ex-data e)) 'do/labeling)))))

(deftest labeling-checks-its-arguments
  ;; `(do/labeling Ctx)` and `(do/labeling Ctx Base)` are the two legal shapes.
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [form [(list 'do/labeling)
                  (list 'do/labeling 42)
                  (list 'do/labeling (tu/tmp-ctx "A") (tu/tmp-ctx "B") (tu/tmp-ctx "C"))]]
      (is (= :not-assertible
             (try (v/assert kb form 'CxUniverse) nil
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
          (str "refused: " (pr-str form))))
    (testing "the two-argument form names the base explicitly"
      (is (map? (v/assert kb (list 'do/labeling (tu/tmp-ctx "Labeling") 'CxUniverse)
                          'CxUniverse))))))

;; ---- 2. the dilemma bridge ---------------------------------------------

(deftest labeling-builds-the-program-settle-declined-to
  ;; The gap this closes. The engine reports the dilemma and builds nothing; the
  ;; imperative builds the Program from that report, which is what `contradictions`
  ;; hands back both sides *for*.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [d (dilemma kb)
          ctx (tu/tmp-ctx "Labeling")]
      (testing "settle built no program for the dilemma"
        (is (= 1 (count (v/contradictions kb))))
        (is (nil? (v/last-program kb))))
      (let [{:keys [program classification]} (v/assert kb (list 'do/labeling ctx) 'CxUniverse)]
        (testing "the imperative built one, over exactly the two contested sides"
          (is (= #{(:positive d) (:negative d)} (:assumptions program)))
          (is (= 1 (count (:contradictions program)))))
        (testing "and recorded it, so last-program and classify now answer"
          (is (some? (v/last-program kb)))
          (is (= classification (label/classify kb))))))))

(deftest a-dilemma-classifies-as-supportable-on-both-sides
  ;; What brave/cautious buys over `in?`: neither side is forced, both are available.
  ;; That is invisible from belief alone — the TMS holds both and says nothing about
  ;; whether either could have been given up.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [d (dilemma kb)
            {:keys [classification]} (v/assert kb (list 'do/labeling (tu/tmp-ctx "Labeling"))
                                               'CxUniverse)]
        (is (= #{(:positive d) (:negative d)} (:supportable classification)))
        (is (empty? (:true classification)))
        (is (empty? (:false classification)))))))

(deftest a-kb-with-no-dilemma-labels-nothing
  ;; Silence is the correct answer, and minting an empty labeling context would assert
  ;; that a choice was made where none was.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [ctx (tu/tmp-ctx "Labeling")
          res (v/assert kb (list 'do/labeling ctx) 'CxUniverse)]
      (is (empty? (:handles res)))
      (is (nil? (:program res)))
      (is (= {:true #{} :supportable #{} :false #{}} (:classification res)))
      (is (empty? (v/sentexes-in-context kb ctx))))))

;; ---- 3. what committing does, and what undoes it ------------------------

(defn- sides-in
  "Which sides of dilemma `d` a level-3 read from `ctx` finds, as `[positive? negative?]`."
  [kb {:keys [pred individual]} ctx]
  [(boolean (seq (v/lookup kb 3 (list pred individual) ctx)))
   (boolean (seq (v/lookup kb 3 (list 'not (list pred individual)) ctx)))])

(deftest labeling-commits-inside-its-context-and-leaves-the-base-alone
  ;; The chosen semantics, stated where it can be read (docs/labeling.md).  `ctx` sees
  ;; the base and the base does not see `ctx`, so the strengthened copy decides the
  ;; dilemma at `ctx` and below and nowhere else (docs/nmtms.md, "A defeat is scoped to
  ;; its vantage").  The engine still refuses to arbitrate on its own, and commits
  ;; inside `ctx` only because a caller wrote the imperative.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [d (dilemma kb)
          ctx (tu/tmp-ctx "Labeling")]
      (is (= {:positive true :negative true :reported 1} (belief-snapshot kb d))
          "before: both sides believed, one dilemma reported")
      (let [{:keys [handles]} (v/assert kb (list 'do/labeling ctx) 'CxUniverse)]
        (testing "the base still believes both sides and reports the one dilemma"
          (is (= {:positive true :negative true :reported 1} (belief-snapshot kb d)))
          (is (and (v/in? kb (:positive d)) (v/in? kb (:negative d)))))
        (testing "inside the labeling context exactly one side survives"
          (let [[pos neg] (sides-in kb d ctx)]
            (is (not= pos neg))))
        (testing "and the labeling context records the surviving side"
          (is (= 1 (count handles))))))))

(deftest a-labeled-context-is-a-queryable-world
  ;; What committing buys over a detached record, and the reason it was chosen: `ctx`
  ;; inherits the uncontested background through `genlCx`, so it can be asked
  ;; about rather than merely read.
  ;;
  ;; Level 3 (`:visible`) throughout, and the level is what makes the reading mean
  ;; anything. `sentexes-matching` is context-exact (level 2) and reports the background
  ;; missing even when it is inherited; level 7 expands rules but drops an answer belief
  ;; holds defeated (`res/defeated-answer?`), so it agrees with level 3 about which side
  ;; of the clash survives and differs only in reach. Level 3 is the belief-filtered
  ;; view of stored facts, which is what "is this world consistent" means.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [pred individual background]} (dilemma kb)
          ctx (tu/tmp-ctx "Labeling")]
      (v/assert kb (list 'do/labeling ctx) 'CxUniverse)
      (testing "ctx sees the base"
        (is (true? (v/sees? kb ctx 'CxUniverse))))
      (testing "the uncontested background is inherited"
        (is (seq (v/lookup kb 3 background ctx)))
        (is (empty? (v/sentexes-matching kb background ctx))
            "and sentexes-matching is context-exact, so it does not show it"))
      (testing "the contested pair is decided: exactly one side survives"
        (let [pos (seq (v/lookup kb 3 (list pred individual) ctx))
              neg (seq (v/lookup kb 3 (list 'not (list pred individual)) ctx))]
          (is (not= (boolean pos) (boolean neg)))))
      (testing "and the base keeps both sides, since the commitment is scoped to ctx"
        (let [pos (seq (v/lookup kb 3 (list pred individual) 'CxUniverse))
              neg (seq (v/lookup kb 3 (list 'not (list pred individual)) 'CxUniverse))]
          (is (and pos neg)))))))

(deftest retracting-a-labeling-revives-the-dilemma-inside-its-context
  ;; The undo path.  Additive, so no `!`; that claim is only true if this holds.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [d (dilemma kb)
          ctx (tu/tmp-ctx "Labeling")
          {:keys [handles]} (v/assert kb (list 'do/labeling ctx) 'CxUniverse)]
      (is (apply not= (sides-in kb d ctx)) "committed inside ctx")
      (run! #(v/retract! kb %) handles)
      (testing "the dilemma is back inside ctx, both sides read again"
        (is (= [true true] (sides-in kb d ctx)))
        (is (= {:positive true :negative true :reported 1} (belief-snapshot kb d)))))))

(deftest rival-labelings-stand-side-by-side
  ;; Each labeling decides the dilemma in its own context and in no other, so two of them
  ;; hold at once as sibling contexts, and the base reports its one dilemma throughout.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [d    (dilemma kb)
          ctx  (tu/tmp-ctx "Labeling")
          ctx2 (tu/tmp-ctx "Rival")
          {h1 :handles} (v/assert kb (list 'do/labeling ctx) 'CxUniverse)
          {h2 :handles} (v/assert kb (list 'do/labeling ctx2) 'CxUniverse)]
      (is (= 1 (count h1)))
      (is (= 1 (count h2)))
      (is (apply not= (sides-in kb d ctx)))
      (is (apply not= (sides-in kb d ctx2)))
      (is (= {:positive true :negative true :reported 1} (belief-snapshot kb d))))))

;; ---- 4. the labeling solve agrees with the classification solve ---------

(deftest the-labeling-is-an-answer-set-of-its-own-classification
  ;; A labeling and its classification are two answers about one program, from two
  ;; separate solves, and they have to agree:
  ;;
  ;;     :true  ⊆ labeled        :false ∩ labeled = ∅
  ;;
  ;; They did not. Classification enumerates optima and so goes straight to the ASP
  ;; backend, ignoring `(:solver kb)`; the labeling used the installed solver, which on
  ;; a default KB is the greedy stub. Two nogoods sharing a member is where greedy
  ;; loses — it spends two defeats where the optimum spends one — and the stub then
  ;; kept an assumption holding in NO optimum while dropping two that hold in EVERY
  ;; one. Under commit semantics that materializes an impossible world.
  ;;
  ;; Built as a Program rather than through a KB because the engine only makes P/¬P
  ;; pairs today, so a shared member is not reachable from `assert` — which is exactly
  ;; why this needs pinning now rather than when it first becomes reachable.
  (when asp?
    (let [content {1 {:sentence '(aaa) :context 'C}   ; shared, sorts first
                   2 {:sentence '(bbb) :context 'C}
                   3 {:sentence '(ccc) :context 'C}}
          program (solve/program #{1 2 3}
                                 [{:nogood #{1 2} :priority 1 :sentence '(contradicts (aaa) (bbb))}
                                  {:nogood #{1 3} :priority 1 :sentence '(contradicts (aaa) (ccc))}]
                                 content)
          c       (label/classify-program program)
          labeled (fn [solver] (let [d (set (:defeat (solve-types/solve solver program)))]
                                 (into #{} (remove d) (:assumptions program))))]
      (testing "the classification is decisive here — one optimum, nothing supportable"
        (is (= #{2 3} (:true c)))
        (is (= #{1} (:false c)))
        (is (empty? (:supportable c))))
      (testing "the greedy stub disagrees with it, which is the bug"
        (is (= #{1} (labeled solve/local-solver))))
      (testing "the ASP edge solver agrees with it, which is the fix"
        (is (= #{2 3} (labeled edge/edge-solver)))))))

(deftest a-kb-labeling-agrees-with-its-classification
  ;; The same invariant on the path a caller actually takes. Weaker than the unit test
  ;; above (a KB dilemma is a plain pair, where greedy and optimal cannot diverge), but
  ;; it is the assertion that keeps holding if the engine ever builds a wider nogood.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (dilemma kb)
      (let [{:keys [program classification handles]}
            (v/assert kb (list 'do/labeling (tu/tmp-ctx "Labeling")) 'CxUniverse)
            labeled (set (map #(:id (v/sentex kb %)) handles))]
        (testing "nothing classified :false was committed to"
          (is (empty? (filter labeled (:false classification)))))
        (testing "and the program's assumptions are the dilemma's two sides"
          (is (= 2 (count (:assumptions program)))))))))

(deftest a-labeling-whose-solve-did-not-finish-is-refused-not-committed
  ;; The classification solve and the labeling solve are two solves, so a budget that
  ;; runs out between them leaves one answered and the other not.  Degrading the
  ;; unanswered half to the stub would commit a world the classification beside it
  ;; contradicts, and `check-agrees` would report it as `:labeling-inconsistent` —
  ;; blaming the encoding for a disagreement the fallback introduced.  The imperative
  ;; refuses instead, and refuses *before* writing anything.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [d   (dilemma kb)
            ctx (tu/tmp-ctx "Labeling")
            real solver/solve
            e (with-redefs [solver/solve (fn [aspif mode]
                                           (if (= mode :label)
                                             {:status :interrupted :atoms [] :cost nil :raw nil}
                                             (real aspif mode)))]
                (is (thrown? clojure.lang.ExceptionInfo
                             (v/assert kb (list 'do/labeling ctx) 'CxUniverse))))]
        (testing "and it names the solver, not the encoding"
          (is (= :solver-failed (:type (ex-data e))))
          (is (= :interrupted (:status (ex-data e)))))
        (testing "nothing was committed: the dilemma still stands, both sides believed"
          (is (= {:positive true :negative true :reported 1} (belief-snapshot kb d))))
        (testing "and no labeling context was minted"
          (is (empty? (v/sentexes-in-context kb ctx))))))))

;; ---- 5. determinism -----------------------------------------------------

(deftest the-labeled-side-does-not-depend-on-assertion-order
  ;; The engine-wide invariant does not get an exception for being inside a solver.
  ;; The two rules are asserted in both orders across two KBs; the labeling must name
  ;; the same *sentence* both times. Comparing sentences rather than handles is the
  ;; whole point — handles are allocated in assertion order, so comparing those would
  ;; pass no matter what the solver did.
  (let [labeled (fn [flip?]
                  (tu/with-neutral-kb [kb tu/fresh]
                    (let [quaker 'tmp_lbl_quaker pacifist 'tmp_lbl_pacifist
                          republican 'tmp_lbl_republican nixon 'TmpLblNixon
                          pos (default-rule (list quaker '?x) (list pacifist '?x))
                          neg (default-rule (list republican '?x)
                                            (list 'not (list pacifist '?x)))]
                      (doseq [r (if flip? [neg pos] [pos neg])]
                        (v/assert kb r 'CxUniverse))
                      (v/assert kb (list quaker nixon) 'CxUniverse)
                      (v/assert kb (list republican nixon) 'CxUniverse)
                      (let [ctx 'CxTmpLblLabeling]
                        (v/assert kb (list 'do/labeling ctx) 'CxUniverse)
                        (set (map :sentence (v/sentexes-in-context kb ctx)))))))]
    (is (= (labeled false) (labeled true))
        "the same knowledge in either order labels the same sentence")))

(deftest a-labeling-that-disagrees-with-its-own-classification-is-refused-by-name
  ;; `check-agrees` guards the boundary between two solves over one program — the failure
  ;; this design is most exposed to, per its own docstring — and refuses with
  ;; `:labeling-inconsistent`.  A genuine disagreement cannot be staged through the
  ;; entry points (two consistent solves is what the solver contract promises), so the guard
  ;; is provoked directly, in both directions it checks.  No solver needed: this is
  ;; the check, not the solve.
  (let [check @#'label/check-agrees]
    (testing "an assumption every optimum keeps, dropped by the labeling"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (check {:fixed #{}} #{} {:true '[a1] :false []})))]
        (is (= :labeling-inconsistent (:type (ex-data e))))
        (is (= '[a1] (:missing-true (ex-data e))))))
    (testing "an assumption no optimum keeps, kept by the labeling"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (check {:fixed #{}} #{'a2} {:true [] :false '[a2]})))]
        (is (= :labeling-inconsistent (:type (ex-data e))))
        (is (= '[a2] (:kept-false (ex-data e))))))
    (testing "and known-true background is never an assumption the labeling owes"
      (is (nil? (check {:fixed #{'bg}} #{} {:true '[bg] :false []}))))))
