;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.labeling-test
  "The `do/` channel and `(do/labeling Ctx)`: an imperative is never stored and never runs
  inside a rule, the dilemma bridge builds the `Program` a settle does not, the commitment
  stays inside `Ctx` (`belief-unmoved` around every labeling), and the labeling agrees with
  its classification.  Classification itself is `asp_label_test`'s."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.label :as label]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.config :as config]
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
  (tu/with-neutral-kb [kb tu/fresh]
    (let [ctx (tu/tmp-ctx "Labeling")
          before (count (v/sentexes-in-context kb 'CxUniverse))]
      (v/assert kb (list 'do/labeling ctx) 'CxUniverse)
      (testing "no sentex was stored for the imperative itself"
        (is (nil? (v/handle-of kb (list 'do/labeling ctx) 'CxUniverse)))
        (is (empty? (v/find-sentexes kb 'do/labeling)))
        (is (= before (count (v/sentexes-in-context kb 'CxUniverse))))))))

(deftest an-imperative-is-refused-inside-a-rule
  ;; every slot a rule has, since the check walks the form
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
  (tu/with-neutral-kb [kb tu/fresh]
    (let [e (try (v/assert kb (list 'do/frobnicate 'X) 'CxUniverse) nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= :not-assertible (:type (ex-data e))))
      (is (contains? (:known (ex-data e)) 'do/labeling)))))

(deftest labeling-checks-its-arguments
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
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [d (dilemma kb)
            {:keys [classification]} (v/assert kb (list 'do/labeling (tu/tmp-ctx "Labeling"))
                                               'CxUniverse)]
        (is (= #{(:positive d) (:negative d)} (:supportable classification)))
        (is (empty? (:true classification)))
        (is (empty? (:false classification)))))))

(deftest a-kb-with-no-dilemma-labels-nothing
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
  (tu/with-neutral-kb [kb tu/fresh]
    (let [d (dilemma kb)
          ctx (tu/tmp-ctx "Labeling")]
      (is (= {:positive true :negative true :reported 1} (belief-snapshot kb d))
          "before: both sides believed, one dilemma reported")
      (let [{:keys [handles]} (v/assert kb (list 'do/labeling ctx) 'CxUniverse)]
        (testing "the base still believes both sides and reports the one dilemma"
          (is (= {:positive true :negative true :reported 1} (belief-snapshot kb d)))
          (is (and (v/believed? kb (:positive d)) (v/believed? kb (:negative d)))))
        (testing "inside the labeling context exactly one side survives"
          (let [[pos neg] (sides-in kb d ctx)]
            (is (not= pos neg))))
        (testing "and the labeling context records the surviving side"
          (is (= 1 (count handles))))))))

(deftest a-labeled-context-is-a-queryable-world
  ;; level 3 throughout: `sentexes-matching` (level 2) is context-exact and misses the
  ;; inherited background (docs/labeling.md, "One caveat about which level you ask at")
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
  ;; a Program, since two nogoods sharing a member, where greedy and optimal diverge,
  ;; are not reachable from `assert`
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
  ;; a KB dilemma is a plain pair, where greedy and optimal cannot diverge
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
  ;; the member cap is lowered so a solve labels the cluster and another classifies it;
  ;; one answered and one not must refuse before anything is written
  (when asp?
    (with-redefs [config/classify-max-cluster-members (constantly 1)]
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
            (is (empty? (v/sentexes-in-context kb ctx)))))))))

(deftest a-labeling-asks-the-installed-solver-only-with-no-backend
  ;; the member cap is lowered so the dilemma's cluster is solved, not enumerated
  (doseq [backend? (if asp? [true false] [false])]
    (testing (str "backend " backend?)
      (with-redefs [solver/available? (constantly backend?)
                    config/classify-max-cluster-members (constantly 1)]
        (tu/with-neutral-kb [kb tu/fresh]
          (let [_ (dilemma kb) called (atom 0) ctx (tu/tmp-ctx "Labeling")]
            (v/set-solver kb (reify solve-types/Solver
                               (solve [_ program]
                                 (swap! called inc)
                                 (solve-types/solve solve/local-solver program))))
            (v/assert kb (list 'do/labeling ctx) 'CxUniverse)
            (is (= (not backend?) (pos? @called)))))))))

(deftest a-labeling-drops-what-its-defeat-drops-by-cascade
  ;; `b` rebuts `a` and `c`, each rebuts `b`; a `Program`'s optima would spend a defeat
  ;; per dilemma (docs/labeling.md, "The labeling and its classification must agree")
  (doseq [backend? (if asp? [true false] [false])]
    (testing (str "backend " backend?)
      (with-redefs [solver/available? (constantly backend?)]
        (tu/with-neutral-kb [kb tu/fresh]
          (let [pa (tu/tmp-pred) pb (tu/tmp-pred) pc (tu/tmp-pred) x (tu/tmp-ind)
                ctx (tu/tmp-ctx "Labeling")]
            (doseq [[p q] [[pa pb] [pb pa] [pc pb] [pb pc]]]
              (v/assert kb (default-rule (list p x) (list 'not (list q x))) 'CxUniverse))
            (doseq [p [pa pb pc]] (v/assert kb (list p x) 'CxUniverse))
            (let [h  #(v/handle-of kb % 'CxUniverse)
                  [a b c na nb nc] (map h [(list pa x) (list pb x) (list pc x)
                                           (list 'not (list pa x)) (list 'not (list pb x))
                                           (list 'not (list pc x))])
                  {:keys [classification]} (v/assert kb (list 'do/labeling ctx) 'CxUniverse)]
              (testing "the classification is the cascade's"
                (is (= #{a c nb} (:true classification)))
                (is (= #{b na nc} (:false classification))))
              (testing "and the labeled context keeps a, c and ¬b"
                (is (= {a true c true nb true b false na false nc false}
                       (into {} (for [[f k] [[(list pa x) a] [(list pc x) c]
                                             [(list 'not (list pb x)) nb] [(list pb x) b]
                                             [(list 'not (list pa x)) na]
                                             [(list 'not (list pc x)) nc]]]
                                  [k (boolean (v/ask? kb f ctx))]))))))))))))

;; ---- 5. determinism -----------------------------------------------------

(deftest the-labeled-side-does-not-depend-on-assertion-order
  ;; the rules in both orders across two KBs; compared by sentence, since handles follow
  ;; assertion order
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
  ;; no entry point stages a disagreement, so the check is called directly, both ways
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
