;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-label-test
  "Brave/cautious classification and labeling contexts (`vaelii.impl.asp.label`).

  The point of these tests is the *relationship to the TMS*, not the solver. A
  classification that disagreed with belief would be worse than none: it would look
  authoritative while contradicting what the engine actually answers. So every
  KB-level test below re-checks the two invariants —

      :true  ⊆ believed        :false ∩ believed = ∅

  — rather than only asserting the classification itself.

  ## What the KB does not supply

  Classification reads `core/last-program`, the tie the engine hands to the solver.
  For a rebuttal there is none: a coexisting `P`/`¬P` pair at `:default` is a
  **represented dilemma**, not a tie to be broken, so `decide-nogood` reports it
  through `contradictions` and never builds a Program (docs/exceptions.md, \"What
  surfaces where\").

  That splits this file cleanly in two, and the split is the useful part.

  Sections 1 and 4 classify hand-built `Program`s. That is where the feature actually
  lives — brave/cautious enumeration over optimal answer sets is a property of the
  encoding and the backend, not of any particular KB — and it is untouched.

  Sections 2 and 3 are KB-level, and what they pin is now the *negative* contract: a
  KB holding a dilemma has arbitrated nothing, so `classify` must report nothing and
  `label-context` must record nothing. Silence is the correct answer, and the risk it
  guards against is real — a classifier that read current belief instead of the
  recorded program would report a dilemma as decided, and `label-context` would
  materialize whichever side happened to be believed, entrenching by accident the very
  choice the engine declines to make.

  The bridge between the halves is `contradictions`: it hands over both sides with
  their justifications, which is exactly the material a `Program` is built from. So an
  application that *wants* to rank a dilemma can still do so through this machinery —
  section 2 shows it — it just has to ask for it rather than have the engine decide
  behind its back.

  Skipped without an ASP backend: `local-solver` returns one labeling and cannot
  enumerate optima, so these would be asserting the fallback, not the feature."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.atoms :as atoms]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.label :as label]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

(defn- check-tms [kb c]
  (testing "cautious beliefs are all believed"
    (is (every? #(jtms/in? (reasoning/tms kb) %) (:true c))))
  (testing "excluded beliefs are believed by nothing"
    (is (not-any? #(jtms/in? (reasoning/tms kb) %) (:false c)))))

(defn- nixon-diamond
  "Assert the canonical rebutting dilemma on gensym'd terms: two equally-specific
  defaults concluding `(pacifist N)` and `(not (pacifist N))`, with neither naming the
  other's case and neither more specific.  Five tests below need this exact shape, and
  the terms are noise in all of them.

  Returns `{:pacifist p :individual N :handles [positive negative]}`."
  [kb]
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon (tu/tmp-ind)]
    (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
    (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    {:pacifist pacifist
     :individual nixon
     :handles [(v/handle-of kb (list pacifist nixon)             'CxUniverse)
               (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)]}))

(defn- program-of-dilemma
  "The `Program` an application would build to rank a reported dilemma: the two
  contested handles, the nogood between them, and what each side asserts.

  This is `contradictions`' promise turned back into the form the solver machinery
  takes — which is the point of reporting both sides rather than deciding between
  them.  The engine declines to arbitrate; the classification machinery is still right
  here for a caller that wants to."
  [{:keys [nogood priority sentence sides]}]
  (solve/program nogood
                 [{:nogood nogood :priority priority :sentence sentence}]
                 (into {} (map (juxt :handle #(select-keys % [:sentence :context]))) sides)))

;; ---- 1. classification of a Program, no KB -----------------------------

(deftest a-shared-member-is-forced-and-its-partners-are-too
  ;; Nogoods {A,B} and {A,C}. Defeating A alone satisfies both for one defeat;
  ;; defeating B and C costs two. So every optimum drops A and keeps B and C —
  ;; nothing here is arbitrary, and the classification should say so.
  (when asp?
    (let [p (solve/program #{1 2 3}
                           [{:nogood #{1 2} :priority 0 :sentence 'A}
                            {:nogood #{1 3} :priority 0 :sentence 'B}]
                           {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}
                            3 {:sentence '(c) :context 'C}})
          c (label/classify-program p)]
      (testing "the shared member is excluded by every optimal labeling"
        (is (= #{1} (:false c))))
      (testing "its two partners are forced"
        (is (= #{2 3} (:true c))))
      (testing "and nothing is left to arbitrary choice"
        (is (empty? (:supportable c)))))))

(deftest a-two-way-tie-is-supportable-on-both-sides
  ;; The case the classification exists for: two optima, so neither side is forced
  ;; and neither is excluded, even though a solve commits to one.
  (when asp?
    (let [p (solve/program #{1 2}
                           [{:nogood #{1 2} :priority 0 :sentence 'X}]
                           {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}})
          c (label/classify-program p)]
      (is (= #{1 2} (:supportable c)))
      (is (empty? (:true c)))
      (is (empty? (:false c))))))

(deftest known-true-background-classifies-as-true
  ;; `fixed` members are never sent to the solver — they hold by assumption. They
  ;; must still come back `:true`, or a caller reading the classification would
  ;; think the engine had no opinion on them.
  (when asp?
    (let [p (solve/program #{1}
                           [{:nogood #{1 9} :priority 0 :sentence 'X}]
                           {1 {:sentence '(a) :context 'C}})]
      (testing "the uncontested member is background"
        (is (= #{9} (:fixed p))))
      (is (contains? (:true (label/classify-program p)) 9)))))

(deftest an-empty-program-classifies-to-nothing
  (is (= {:true #{} :supportable #{} :false #{}}
         (label/classify-program (solve/program #{} [] {})))))

;; ---- 2. a settled KB has arbitrated nothing to classify ----------------

(deftest a-nixon-diamond-classifies-as-nothing-because-nothing-was-decided
  ;; Both sides of this tie are equally available — that has not changed.  What
  ;; changed is who says so.  The engine keeps both beliefs and reports the pair
  ;; through `contradictions`, so there is no arbitration for `classify` to describe,
  ;; and reporting `:supportable` would be an invention: `:supportable` means "the
  ;; solver picked one of these", and no solver picked anything.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/set-solver kb edge/edge-solver)
      (let [{[pos neg] :handles} (nixon-diamond kb)
            c (label/classify kb)]
        (testing "the engine committed to neither side"
          (is (true? (v/in? kb pos)))
          (is (true? (v/in? kb neg))))
        (testing "so nothing was arbitrated and nothing is classified"
          (is (nil? (v/last-program kb)))
          (is (= {:true #{} :supportable #{} :false #{}} c)))
        (check-tms kb c)))))

(deftest the-arbitrariness-is-still-classifiable-from-the-reported-dilemma
  ;; In a Nixon diamond *neither* side is forced and *neither* is excluded, and it is
  ;; the application's question to ask rather than the engine's to answer:
  ;; `contradictions` hands over both sides with their justifications, which is exactly
  ;; what a `Program` is made of, and classifying that says what the engine deliberately
  ;; declines to say.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [{[pos neg] :handles} (nixon-diamond kb)
            dilemma (first (v/contradictions kb))
            c (label/classify-program (program-of-dilemma dilemma))]
        (testing "the dilemma carries both contestants"
          (is (= #{pos neg} (:nogood dilemma))))
        (testing "and neither is forced or excluded — both are merely supportable"
          (is (= #{pos neg} (:supportable c)))
          (is (empty? (:true c)))
          (is (empty? (:false c))))
        (testing "which agrees with belief, since the engine holds both"
          (is (every? #(jtms/in? (reasoning/tms kb) %) (:supportable c)))
          (check-tms kb c))))))

(deftest a-contradiction-settled-by-strength-never-reaches-the-solver
  ;; A monotonic negation beats a default outright: `decide-nogood` defeats the
  ;; weaker side directly, so no Program is ever built. Classification must report
  ;; nothing arbitrary rather than inventing a tie.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [bird (tu/tmp-type) flies (tu/tmp-pred) tweety (tu/tmp-ind)]
        (v/set-solver kb edge/edge-solver)
        (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
        (v/assert kb (list bird tweety) 'CxUniverse)
        (v/assert kb (list 'not (list flies tweety)) 'CxUniverse {:strength :monotonic})
        (testing "the default lost, and not by arbitration"
          (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxUniverse)))
          (is (nil? (v/last-program kb))))
        (testing "so there is nothing to classify"
          (is (= {:true #{} :supportable #{} :false #{}} (label/classify kb))))))))

(deftest a-dilemma-erases-no-evidence-so-there-is-nothing-to-record
  ;; The inverse of the property `last-program` exists for.  Arbitration destroyed its
  ;; own evidence: the defeated side stopped matching, so the nogood was no longer
  ;; derivable from the KB and had to be recorded *before* belief moved, or the
  ;; arbitrariness became unreportable.
  ;;
  ;; A dilemma moves no belief.  Both sides still match, so the contested pair is
  ;; readable straight off the KB whenever it is asked for — which is why
  ;; `contradictions` can be a live reader while `last-program` had to be a recording.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/set-solver kb edge/edge-solver)
      (let [{:keys [pacifist individual]} (nixon-diamond kb)]
        (testing "both sides still match — settling erased nothing"
          (is (seq (v/sentexes-matching kb (list pacifist individual) 'CxUniverse)))
          (is (seq (v/sentexes-matching kb (list 'not (list pacifist individual)) 'CxUniverse))))
        (testing "so the contested pair is derivable now, not only from a record"
          (let [ds (v/contradictions kb)]
            (is (= 1 (count ds)))
            (is (= 2 (count (:sides (first ds)))))))
        (testing "and there is no recorded program, because no tie was handed over"
          (is (nil? (v/last-program kb))))))))

;; ---- 3. the labeling context -------------------------------------------

(deftest label-context-records-nothing-when-nothing-was-arbitrated
  ;; `label-context` materializes the labeling the engine *committed to*, read from the
  ;; recorded program's assumptions.  A dilemma produces no program and no commitment,
  ;; so an empty record is the honest result.
  ;;
  ;; The failure this guards against is specific and tempting: `label-context` could
  ;; read current belief instead of the recorded program, find both sides IN, and write
  ;; them both — or pick one.  Either puts a decision in the KB that nothing in the KB
  ;; supports, and the labeling context is exactly where such a decision would look
  ;; authoritative.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/set-solver kb edge/edge-solver)
      (let [ctx (tu/tmp-ctx)]
        (nixon-diamond kb)
        (let [{:keys [handles]} (label/label-context kb ctx 'CxUniverse)]
          (testing "the context is still minted as a specialization that sees its base"
            (is (seq (v/sentexes-matching kb (list 'genlCx ctx 'CxUniverse) '?ctx))))
          (testing "but it records no labeling, because there was none to record"
            (is (empty? handles))
            (is (zero? (v/count-in-context kb ctx)))
            (is (empty? (v/sentexes-in-context kb ctx)))))))))

(deftest labeling-does-not-entrench-a-side-of-a-dilemma
  ;; Labeling an *arbitrated* tie entrenches it, and soundly: the record is an ordinary
  ;; assertion, an assertion is evidence, and the recorded side gains a second nogood
  ;; against its rival, so a tie that classifies open beforehand classifies as decided
  ;; after.  Something really was decided.
  ;;
  ;; A dilemma decides nothing, so there is nothing to entrench, and that must stay
  ;; true — the more important direction of the same property.  If
  ;; `label-context` ever wrote a side of a dilemma, this is where it shows: belief
  ;; would move off the pair, or the pair would stop being reported.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/set-solver kb edge/edge-solver)
      (let [ctx (tu/tmp-ctx)
            {[pos neg] :handles} (nixon-diamond kb)
            before (v/contradictions kb)]
        (testing "open on both sides beforehand"
          (is (= 1 (count before)))
          (is (true? (v/in? kb pos)))
          (is (true? (v/in? kb neg))))
        (label/label-context kb ctx 'CxUniverse)
        (testing "and open on both sides afterwards — belief did not move"
          (is (true? (v/in? kb pos)))
          (is (true? (v/in? kb neg)))
          (is (= :default (v/defeat-class kb pos)))
          (is (= :default (v/defeat-class kb neg))))
        (testing "the dilemma is still reported, unchanged"
          (is (= (map :nogood before) (map :nogood (v/contradictions kb)))))
        (testing "and classification still claims nothing"
          (let [after (label/classify kb)]
            (is (= {:true #{} :supportable #{} :false #{}} after))
            (check-tms kb after)))))))

(deftest label-context-is-additive-and-retractable
  ;; No `!` in the name, so it must genuinely undo: the neutral fixture retracting the
  ;; test's premises has to take the labeling context with it.  The `genlCx` edge
  ;; is the one premise `label-context` writes unconditionally, so it is what teardown
  ;; has to reclaim — and the taxonomy closure it feeds has to let go of it too.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/set-solver kb edge/edge-solver)
      (let [ctx (tu/tmp-ctx)]
        (nixon-diamond kb)
        (label/label-context kb ctx 'CxUniverse)
        (is (seq (v/sentexes-matching kb (list 'genlCx ctx 'CxUniverse) '?ctx)))
        (is (v/sees? kb ctx 'CxUniverse))))))

;; ---- 4. known-true content is background, never contested --------------

(deftest known-true-content-is-never-a-side-of-a-dilemma
  ;; The split the whole design rests on: `:default` content is what is contested,
  ;; `:monotonic` content is the background it is contested *against*.
  ;; It is the reporting surface's duty as much as arbitration's — a solver able to
  ;; withdraw known-true content would be deciding the premises, and a report that
  ;; offered one up invites the same.  A dilemma names only defeasible sides, so an
  ;; application handed one
  ;; cannot be led to give up something the KB knows.
  ;;
  ;; The monotonic fact is about the contested individual on purpose: entanglement by
  ;; shared terms is what a sloppy nogood would sweep in.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/set-solver kb edge/edge-solver)
      (let [{:keys [individual] [pos neg] :handles} (nixon-diamond kb)
            person (tu/tmp-type)
            _ (v/assert kb (list person individual) 'CxUniverse {:strength :monotonic})
            mono (v/handle-of kb (list person individual) 'CxUniverse)
            dilemma (first (v/contradictions kb))]
        (testing "the dilemma names exactly the two defaults"
          (is (= #{pos neg} (:nogood dilemma)))
          (is (not (contains? (:nogood dilemma) mono)))
          (is (every? #(= :default (:defeat-class %)) (:sides dilemma))))
        (testing "and the entangled known-true fact stands, unclassed by the dilemma"
          (is (= :monotonic (v/defeat-class kb mono)))
          (is (seq (v/sentexes-matching kb (list person individual) 'CxUniverse))))
        (testing "so a program built from the dilemma gives atoms to the defaults only"
          ;; the assertion a recorded program carries, at the boundary where a
          ;; caller crosses into the solver
          (let [t (:table (edge/translate (program-of-dilemma dilemma)))]
            (is (every? #(some? (atoms/atom-of-sentex t %)) [pos neg]))
            (is (nil? (atoms/atom-of-sentex t mono)))))))))

(deftest a-strength-decided-clash-never-builds-a-program
  ;; The other half: when classes differ, `decide-nogood` defeats the weaker side
  ;; directly. Nothing is contested, so nothing is sent — a monotonic belief is
  ;; never an atom, not even a fixed one.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [bird (tu/tmp-type) flies (tu/tmp-pred) tweety (tu/tmp-ind)]
        (v/set-solver kb edge/edge-solver)
        (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
        (v/assert kb (list bird tweety) 'CxUniverse)
        (v/assert kb (list 'not (list flies tweety)) 'CxUniverse {:strength :monotonic})
        (testing "the monotonic side won without a solve"
          (is (nil? (v/last-program kb)))
          (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxUniverse)))
          (is (seq (v/sentexes-matching kb (list 'not (list flies tweety)) 'CxUniverse))))))))

(deftest a-rogue-solver-moves-neither-belief-nor-classification
  ;; `set-solver` takes any implementation, so the engine has to be safe against a bad
  ;; one.  It is safe by construction rather than by clamping the solver's *output* to
  ;; the assumptions its program offered: a plain rebuttal is never offered to a solver
  ;; at all.
  ;;
  ;; The solver installed here would withdraw a known-true belief it was never handed,
  ;; given the chance.  Counting its calls is what turns "it behaved" into "it was
  ;; never asked" — the stronger claim, and the one that breaks first if arbitration is
  ;; quietly restored.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [happy (tu/tmp-pred) tom (tu/tmp-ind) called (atom 0)]
        (v/assert kb (list happy tom) 'CxUniverse {:strength :monotonic})
        (let [monotonic (v/handle-of kb (list happy tom) 'CxUniverse)]
          (v/set-solver kb
                        (reify solve-types/Solver
                          (solve [_ {:keys [assumptions]}]
                            (swap! called inc)
                            {:defeat (conj (set (take 1 (sort assumptions))) monotonic)
                             :violated []})))
          (let [{[pos neg] :handles} (nixon-diamond kb)]
            (testing "the solver was never consulted"
              (is (zero? @called))
              (is (nil? (v/last-program kb))))
            (testing "so the known-true belief stands, never having been at risk"
              (is (seq (v/sentexes-matching kb (list happy tom) 'CxUniverse)))
              (is (jtms/in? (reasoning/tms kb) monotonic)))
            (testing "and both sides of the dilemma stand, undecided by the plugin"
              (is (true? (v/in? kb pos)))
              (is (true? (v/in? kb neg)))
              (is (= 1 (count (v/contradictions kb)))))
            (testing "while classification claims nothing it cannot support"
              (let [c (label/classify kb)]
                (is (= {:true #{} :supportable #{} :false #{}} c))
                (check-tms kb c)))))))))
