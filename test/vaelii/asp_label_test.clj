;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-label-test
  "`vaelii.impl.asp.label`'s `classify` and `label-context`.  Sections 1 and 4 classify
  hand-built `Program`s; sections 2 and 3 check that a KB holding a dilemma has recorded no
  program, so `classify` reports nothing and `label-context` records nothing, and that a
  program built from `contradictions` classifies.  Each KB-level test re-checks
  `:true ⊆ believed` and `:false ∩ believed = ∅` (`check-tms`).  Skipped without an ASP
  backend, since `local-solver` cannot enumerate optima."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.atoms :as atoms]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.label :as label]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- check-tms [kb c]
  (testing "cautious beliefs are all believed"
    (is (every? #(jtms/in? (reasoning/tms kb) %) (:true c))))
  (testing "excluded beliefs are believed by nothing"
    (is (not-any? #(jtms/in? (reasoning/tms kb) %) (:false c)))))

(defn- nixon-diamond
  "Assert the canonical rebutting dilemma on gensym'd terms: two equally-specific
  defaults concluding `(pacifist N)` and `(not (pacifist N))`, with neither naming the
  other's case and neither more specific.

  Returns `{:pacifist p :individual N :handles [positive negative]}`."
  [kb]
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon (tu/tmp-ind)]
    (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
    (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    {:pacifist pacifist
     :individual nixon
     :handles [(v/handle-of kb (list pacifist nixon)             'CxUniverse)
               (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)]}))

(defn- program-of-dilemma
  "The `Program` an application would build to rank a reported dilemma: the two
  contested handles, the nogood between them, and what each side asserts."
  [{:keys [nogood priority sentence sides]}]
  (solve/program nogood
                 [{:nogood nogood :priority priority :sentence sentence}]
                 (into {} (map (juxt :handle #(select-keys % [:sentence :context]))) sides)))

;; ---- 1. classification of a Program, no KB -----------------------------

(deftest a-shared-member-is-forced-and-its-partners-are-too
  ;; nogoods {A,B} and {A,C}: dropping A costs one defeat, B and C two
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
  (when asp?
    (let [p (solve/program #{1 2}
                           [{:nogood #{1 2} :priority 0 :sentence 'X}]
                           {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}})
          c (label/classify-program p)]
      (is (= #{1 2} (:supportable c)))
      (is (empty? (:true c)))
      (is (empty? (:false c))))))

(deftest known-true-background-classifies-as-true
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
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/set-solver kb edge/edge-solver)
      (let [{[pos neg] :handles} (nixon-diamond kb)
            c (label/classify kb)]
        (testing "the engine committed to neither side"
          (is (true? (v/believed? kb pos)))
          (is (true? (v/believed? kb neg))))
        (testing "so nothing was arbitrated and nothing is classified"
          (is (nil? (v/last-program kb)))
          (is (= {:true #{} :supportable #{} :false #{}} c)))
        (check-tms kb c)))))

(deftest the-arbitrariness-is-still-classifiable-from-the-reported-dilemma
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
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [bird (tu/tmp-type) flies (tu/tmp-pred) tweety (tu/tmp-ind)]
        (v/set-solver kb edge/edge-solver)
        (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
        (v/assert kb (list bird tweety) 'CxUniverse)
        (v/assert kb (list 'not (list flies tweety)) 'CxUniverse {:strength :monotonic})
        (testing "the default lost, and not by arbitration"
          (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxUniverse)))
          (is (nil? (v/last-program kb))))
        (testing "so there is nothing to classify"
          (is (= {:true #{} :supportable #{} :false #{}} (label/classify kb))))))))

(deftest a-dilemma-erases-no-evidence-so-there-is-nothing-to-record
  ;; both sides still match, so `contradictions` reads the pair live and nothing records it
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
  ;; reading current belief instead of the recorded program would find both sides IN
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
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/set-solver kb edge/edge-solver)
      (let [ctx (tu/tmp-ctx)
            {[pos neg] :handles} (nixon-diamond kb)
            before (v/contradictions kb)]
        (testing "open on both sides beforehand"
          (is (= 1 (count before)))
          (is (true? (v/believed? kb pos)))
          (is (true? (v/believed? kb neg))))
        (label/label-context kb ctx 'CxUniverse)
        (testing "and open on both sides afterwards — belief did not move"
          (is (true? (v/believed? kb pos)))
          (is (true? (v/believed? kb neg)))
          (is (= :default (v/defeat-class kb pos)))
          (is (= :default (v/defeat-class kb neg))))
        (testing "the dilemma is still reported, unchanged"
          (is (= (map :nogood before) (map :nogood (v/contradictions kb)))))
        (testing "and classification still claims nothing"
          (let [after (label/classify kb)]
            (is (= {:true #{} :supportable #{} :false #{}} after))
            (check-tms kb after)))))))

(deftest label-context-copies-the-side-label-dilemmas-kept-while-its-own-context-believes-it
  ;; copying every IN assumption would copy both sides of the dilemma
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{hs :handles} (nixon-diamond kb)
          [pick rec rec2] (repeatedly 3 tu/tmp-ctx)
          sentences (fn [r] (mapv #(:sentence (v/sentex kb %)) (:handles r)))
          kept      (sentences (label/label-dilemmas kb pick 'CxUniverse))
          rival     (first (remove #(= kept [(:sentence (v/sentex kb %))]) hs))]
      (is (= 1 (count kept)))
      (let [r (label/label-context kb rec 'CxUniverse)]
        (is (= kept (sentences r)))
        (is (= [:monotonic] (mapv #(:strength (v/sentex kb %)) (:handles r)))
            "each copy is monotonic, so it out-ranks the rival inside the labeling context")
        (is (not (v/ask? kb (:sentence (v/sentex kb rival)) rec))))
      (v/assert kb (:sentence (v/sentex kb rival)) 'CxUniverse {:strength :monotonic})
      (is (= [] (sentences (label/label-context kb rec2 'CxUniverse)))
          "the rival restated at monotonic defeats the kept side where it is stored"))))

(deftest a-labeling-copy-and-a-monotonic-rival-are-a-hard-clash-in-the-labeling-context-in-either-order
  ;; label-context's copy in rec, label-dilemmas' copy in pick and the rival restated in
  ;; the base are each monotonic, so each copy clashes with the rival.  The rival-first
  ;; order writes label-context's two sentences itself: label-context reads belief, and
  ;; copies nothing once the rival is restated (the test above).
  (let [reading
        (fn [rival-first?]
          (tu/with-neutral-kb [kb tu/fresh]
            (let [{hs :handles} (nixon-diamond kb)
                  [pick rec] (repeatedly 2 tu/tmp-ctx)
                  M      {:strength :monotonic}
                  picked (first (:handles (label/label-dilemmas kb pick 'CxUniverse)))
                  kept   (:sentence (v/sentex kb picked))
                  rival  (first (remove #{kept} (map #(:sentence (v/sentex kb %)) hs)))
                  rival! #(v/assert kb rival 'CxUniverse M)
                  copy   (if rival-first?
                           (do (rival!)
                               (v/assert kb (list 'genlCx rec 'CxUniverse) 'CxUniverse M)
                               (v/assert kb kept rec M))
                           (let [h (first (:handles (label/label-context kb rec 'CxUniverse)))]
                             (rival!)
                             h))
                  rh     (v/handle-of kb rival 'CxUniverse)
                  sides  (fn [c] (set (map :handle (:sides c))))]
              {:at-rec   [(v/believed? kb copy rec) (v/believed? kb rh rec)
                          (v/ask? kb kept rec) (v/ask? kb rival rec)]
               :at-base [(v/ask? kb kept 'CxUniverse) (v/ask? kb rival 'CxUniverse)]
               :conflicts (set (map sides (v/conflicts kb)))
               :expected-sides #{#{picked rh} #{copy rh}}})))
        readings (map reading [false true])]
    (doseq [{:keys [at-rec at-base conflicts expected-sides]} readings]
      (is (= [true true true true] at-rec) "both sides stay believed in the labeling context")
      (is (= [false true] at-base) "the base believes the rival alone")
      (is (= expected-sides conflicts) "conflicts reports each copy against the rival"))
    (is (apply = (map #(dissoc % :expected-sides :conflicts) readings)))))

(deftest label-context-is-additive-and-retractable
  ;; the neutral teardown retracts the `genlCx` edge, the one premise written
  ;; unconditionally, and the closure lets it go
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
  ;; the monotonic fact names the contested individual, the term a nogood built off
  ;; shared terms would take in
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
          (let [t (:table (edge/translate (program-of-dilemma dilemma)))]
            (is (every? #(some? (atoms/atom-of-sentex t %)) [pos neg]))
            (is (nil? (atoms/atom-of-sentex t mono)))))))))

(deftest a-strength-decided-clash-never-builds-a-program
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [bird (tu/tmp-type) flies (tu/tmp-pred) tweety (tu/tmp-ind)]
        (v/set-solver kb edge/edge-solver)
        (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
        (v/assert kb (list bird tweety) 'CxUniverse)
        (v/assert kb (list 'not (list flies tweety)) 'CxUniverse {:strength :monotonic})
        (testing "the monotonic side won without a solve"
          (is (nil? (v/last-program kb)))
          (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxUniverse)))
          (is (seq (v/sentexes-matching kb (list 'not (list flies tweety)) 'CxUniverse))))))))

(deftest a-rogue-solver-moves-neither-belief-nor-classification
  ;; the installed solver would withdraw a known-true handle; counting its calls checks
  ;; that it is never asked
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
              (is (true? (v/believed? kb pos)))
              (is (true? (v/believed? kb neg)))
              (is (= 1 (count (v/contradictions kb)))))
            (testing "while classification claims nothing it cannot support"
              (let [c (label/classify kb)]
                (is (= {:true #{} :supportable #{} :false #{}} c))
                (check-tms kb c)))))))))
