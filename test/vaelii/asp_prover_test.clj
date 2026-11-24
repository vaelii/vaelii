;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-prover-test
  "The `(bravely S)` / `(cautiously S)` prover (`vaelii.impl.asp.prover`, opted in with
  `add-reasoner :brave-cautious`): a read-path brave/cautious classification of the current
  dilemmas that commits nothing.  Backend-dependent tests need a real solver to enumerate
  optima; the solve-free tests force the no-backend path (`with-redefs` on
  `solver/available?`) so they read the JTMS bracket (`label/classify-local`) and run
  everywhere, and the not-assertible refusal is backend-independent too."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.label :as label]
            [vaelii.impl.asp.prover :as prover]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.config :as config]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- nixon-diamond
  "The canonical rebutting dilemma on gensym'd terms: two equally-specific defaults
  concluding `(pacifist N)` and `(not (pacifist N))`.  Returns the terms and both handles."
  [kb]
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon  (tu/tmp-ind)]
    (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
    (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    {:quaker quaker :pacifist pacifist :nixon nixon
     :pos (v/handle-of kb (list pacifist nixon)             'CxUniverse)
     :neg (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)}))

(defn- bare-rule
  "A monotone forward rule — no defeasibility of its own, so it fires from a believed
  antecedent whichever side of a dilemma that belief rests on."
  [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- extended-nixon
  "A Nixon diamond with two downstream conclusions: `ethical` follows from **either**
  side of the `pacifist`/`¬pacifist` dilemma (so it holds under every resolution), and
  `opposes` follows from the pacifist side **only** (so it holds under some resolution and
  not others).  Returns the sentences and handles the tests read."
  [kb]
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        ethical (tu/tmp-pred) opposes (tu/tmp-pred) nixon (tu/tmp-ind)]
    (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
    (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (bare-rule [(list pacifist '?x)]             (list ethical '?x)) 'CxUniverse)
    (v/assert kb (bare-rule [(list 'not (list pacifist '?x))] (list ethical '?x)) 'CxUniverse)
    (v/assert kb (bare-rule [(list pacifist '?x)]             (list opposes '?x)) 'CxUniverse)
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    {:nixon nixon
     :pos-form   (list pacifist nixon)
     :neg-form   (list 'not (list pacifist nixon))
     :ethical-form (list ethical nixon)
     :opposes-form (list opposes nixon)
     :quaker-form  (list quaker nixon)
     :pos     (v/handle-of kb (list pacifist nixon)             'CxUniverse)
     :neg     (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)
     :ethical (v/handle-of kb (list ethical nixon) 'CxUniverse)
     :opposes (v/handle-of kb (list opposes nixon) 'CxUniverse)
     :quaker  (v/handle-of kb (list quaker nixon)  'CxUniverse)}))

(deftest brave-cautious-separates-forced-from-arbitrary
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [pacifist nixon pos neg]} (nixon-diamond kb)
            P  (list pacifist nixon)
            nP (list 'not (list pacifist nixon))]
        (testing "the engine arbitrated nothing: both sides IN, no program"
          (is (true? (v/believed? kb pos)))
          (is (true? (v/believed? kb neg)))
          (is (nil? (v/last-program kb))))
        (testing "each side is bravely true (in some optimum)"
          (is (v/ask? kb (list 'bravely P)  'CxUniverse))
          (is (v/ask? kb (list 'bravely nP) 'CxUniverse)))
        (testing "neither side is cautiously true (in every optimum) — the arbitrariness"
          (is (not (v/ask? kb (list 'cautiously P)  'CxUniverse)))
          (is (not (v/ask? kb (list 'cautiously nP) 'CxUniverse))))
        (testing "the read committed nothing — belief and reports are unchanged"
          (is (true? (v/believed? kb pos)))
          (is (true? (v/believed? kb neg)))
          (is (= 1 (count (v/contradictions kb))))
          (is (nil? (v/last-program kb))))))))

(deftest an-uncontested-fact-is-both-brave-and-cautious
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [quaker nixon]} (nixon-diamond kb)
            fact (list quaker nixon)]
        (is (v/ask? kb (list 'cautiously fact) 'CxUniverse))
        (is (v/ask? kb (list 'bravely fact)    'CxUniverse))))))

(deftest bravely-and-cautiously-are-not-assertible
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [f '[bravely cautiously]]
      (testing (str f " is refused as an assertion")
        (let [e (try (v/assert kb (list f (list 'some_prop 'Thing)) 'CxUniverse) nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (some? e) (str "asserting (" f " ...) should throw"))
          (is (= :not-well-formed (:type (ex-data e))))
          (is (str/includes? (ex-message e) (str f " is not assertible"))))))))

(deftest a-brave-cautious-antecedent-derives-nothing
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [pacifist nixon]} (nixon-diamond kb)]
        (v/assert kb (list 'set/forwardRule
                           (vr/rule-sentence [(list 'bravely (list pacifist nixon))]
                                             (list 'suspected_pacifist nixon)))
                  'CxUniverse)
        (is (not (v/ask? kb (list 'suspected_pacifist nixon) 'CxUniverse)))))))

(deftest the-reader-is-opt-in
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [{:keys [pacifist nixon]} (nixon-diamond kb)]
        (is (not (v/ask? kb (list 'bravely (list pacifist nixon)) 'CxUniverse)))))))

(deftest add-prover-registers-it-directly
  ;; `add-reasoner :brave-cautious` resolves to this constructor; `add-prover` takes the
  ;; value directly, the lower-level route the shipped reasoners are also registered by.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-prover kb (prover/brave-cautious-prover))
      (let [{:keys [pacifist nixon]} (nixon-diamond kb)]
        (is (v/ask? kb (list 'bravely    (list pacifist nixon)) 'CxUniverse))
        (is (not (v/ask? kb (list 'cautiously (list pacifist nixon)) 'CxUniverse)))))))

(defn- modal?
  "Does `(m s)` hold at `ctx`, as a boolean, so a failing `is` prints the question and not
  the KB."
  [kb m s ctx]
  (boolean (v/ask? kb (list m s) ctx)))

(deftest brave-and-cautious-read-the-datum-the-asking-context-sees
  ;; A datum stored in a parent and no dilemma anywhere: a child reads it in every
  ;; labeling, and a sibling that does not see the parent reads it in none.
  (tu/with-neutral-kb [kb tu/fresh]
    (v/add-reasoner kb :brave-cautious)
    (tu/with-terms [glad Pat CxParent CxChild CxSibling]
      (v/assert kb (list 'genlCx CxParent 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse)
      (v/assert kb (list 'genlCx CxSibling 'CxUniverse) 'CxUniverse)
      (v/assert kb (list glad Pat) CxParent)
      (doseq [m '[bravely cautiously]]
        (is (modal? kb m (list glad Pat) CxChild) (str m " in the child"))
        (is (not (modal? kb m (list glad Pat) CxSibling)) (str m " in the sibling"))))))

(deftest a-datum-a-placed-defeat-hides-from-the-reader-is-neither-brave-nor-cautious
  ;; A monotonic denial in the child defeats the parent's default there and below, and the
  ;; default stays IN in the network for the parent.  No dilemma moves it, so its answer
  ;; is its belief as the asking context reads it (`res/believed-at?`), not `jtms/in?`.
  (tu/with-neutral-kb [kb tu/fresh]
    (v/add-reasoner kb :brave-cautious)
    (tu/with-terms [glad Pat CxParent CxChild]
      (v/assert kb (list 'genlCx CxParent 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse)
      (v/assert kb (list glad Pat) CxParent)
      (v/assert kb (list 'not (list glad Pat)) CxChild {:strength :monotonic})
      (is (v/believed? kb (v/handle-of kb (list glad Pat) CxParent)))
      (doseq [m '[bravely cautiously]]
        (is (modal? kb m (list glad Pat) CxParent) (str m " in the parent"))
        (is (not (modal? kb m (list glad Pat) CxChild)) (str m " in the child"))
        (is (modal? kb m (list 'not (list glad Pat)) CxChild) (str m " denial in the child"))))))

;; ---- the solve-free bracket (no backend needed) --------------------------
;; the JTMS read and the bracket's scaling are `grounded_in_region_test`'s

(deftest classify-local-brackets-the-dilemma
  ;; the monotonic background is in no class; the prover reads it off belief
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [pos neg ethical opposes quaker]} (extended-nixon kb)
          cls (label/classify-local kb)]
      (is (some? cls))
      (is (= #{} (:false cls)))
      (testing "a conclusion that holds either way is skeptical"
        (is (contains? (:true cls) ethical))
        (is (not (contains? (:supportable cls) ethical))))
      (testing "the dilemma sides and a one-sided conclusion are credulous-only"
        (is (contains? (:supportable cls) pos))
        (is (contains? (:supportable cls) neg))
        (is (contains? (:supportable cls) opposes))    ; rests on the pacifist side alone
        (is (not (contains? (:true cls) pos)))
        (is (not (contains? (:true cls) opposes))))
      (testing "monotonic background is in neither bracket"
        (is (not (contains? (:supportable cls) quaker)))
        (is (not (contains? (:true cls) quaker)))))))

(deftest classify-local-classifies-only-a-datum-the-reader-believes
  ;; A monotonic denial defeats the one-sided conclusion, which stays IN in the network.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [opposes opposes-form ethical]} (extended-nixon kb)
          cx    (tu/tmp-ctx "Child")
          deny  #(v/assert kb (list 'not opposes-form) % {:strength :monotonic})
          class (fn [cls h] (some #(when (contains? (get cls %) h) %) [:true :supportable :false]))
          read  #(mapv (partial class (apply label/classify-local kb %&)) [opposes ethical])]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (deny cx)
      (is (= [:supportable :true] (read)) "its own context believes it")
      (is (= [nil :true] (read cx)) "the denial defeats it in the child")
      (deny 'CxUniverse)
      (is (= [nil :true] (read))))))

(defn- extended-nixon-reads
  "The brave/cautious reads over `extended-nixon`, which both classification paths owe: a
  one-sided downstream conclusion is not cautious — where base belief alone, believing
  both dilemma sides, would report it cautious."
  []
  (tu/with-neutral-kb [kb tu/fresh]
    (v/add-reasoner kb :brave-cautious)
    (let [{:keys [pos-form neg-form ethical-form opposes-form quaker-form]} (extended-nixon kb)]
      (testing "each dilemma side is bravely true, not cautiously"
        (is (v/ask? kb (list 'bravely    pos-form) 'CxUniverse))
        (is (v/ask? kb (list 'bravely    neg-form) 'CxUniverse))
        (is (not (v/ask? kb (list 'cautiously pos-form) 'CxUniverse)))
        (is (not (v/ask? kb (list 'cautiously neg-form) 'CxUniverse))))
      (testing "a conclusion drawn from both sides is cautiously true — it holds either way"
        (is (v/ask? kb (list 'bravely    ethical-form) 'CxUniverse))
        (is (v/ask? kb (list 'cautiously ethical-form) 'CxUniverse)))
      (testing "a one-sided downstream conclusion is bravely true but not cautiously"
        (is (v/ask? kb (list 'bravely    opposes-form) 'CxUniverse))
        (is (not (v/ask? kb (list 'cautiously opposes-form) 'CxUniverse))))
      (testing "the monotonic background is both brave and cautious"
        (is (v/ask? kb (list 'bravely    quaker-form) 'CxUniverse))
        (is (v/ask? kb (list 'cautiously quaker-form) 'CxUniverse))))))

(deftest solve-free-brave-cautious
  (with-redefs [solver/available? (constantly false)]
    (extended-nixon-reads)))

(deftest backend-brave-cautious-on-derived-conclusions
  ;; With a backend the members come from `classify-program`, which holds members only; a
  ;; derived conclusion is read off `classify-local`, so the two paths answer alike.
  (when asp?
    (extended-nixon-reads)))

(deftest the-backend-classifies-the-asked-datums-component-once-per-write
  ;; the member cap is lowered so a Nixon diamond is past it
  (when asp?
    (with-redefs [config/classify-max-cluster-members (constantly 1)]
      (tu/with-neutral-kb [kb tu/fresh]
        (v/add-reasoner kb :brave-cautious)
        (let [{:keys [pacifist nixon]} (first (doall (repeatedly 3 #(nixon-diamond kb))))
              P        (list pacifist nixon)
              sizes    (atom [])
              classify label/classify-program]
          (with-redefs [label/classify-program
                        (fn [program]
                          (swap! sizes conj (count (:assumptions program)))
                          (classify program))]
            (is (v/ask? kb (list 'bravely P) 'CxUniverse))
            (is (not (v/ask? kb (list 'cautiously P) 'CxUniverse))))
          (is (= [2] @sizes)))))))

(deftest the-solve-free-bracket-runs-once-per-write
  (with-redefs [solver/available? (constantly false)]
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [pacifist nixon]} (nixon-diamond kb)
            P     (list pacifist nixon)
            runs  (atom 0)
            local label/classify-local]
        (with-redefs [label/classify-local (fn [& args] (swap! runs inc) (apply local args))]
          (is (v/ask? kb (list 'bravely P) 'CxUniverse))
          (is (not (v/ask? kb (list 'cautiously P) 'CxUniverse)))
          (is (= 1 @runs) "two asks, no write between")
          (v/assert kb (list (tu/tmp-type) (tu/tmp-ind)) 'CxUniverse)
          (is (v/ask? kb (list 'bravely P) 'CxUniverse))
          (is (= 2 @runs) "a write moves the change clock"))))))

(deftest a-both-sided-conclusion-is-an-ordinary-believed-sentex
  ;; `why` derives the both-sided conclusion from each side, with no reasoner and no backend
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [ethical ethical-form pos neg]} (extended-nixon kb)]
      (testing "it answers an ordinary query"
        (is (true? (v/believed? kb ethical)))
        (is (v/ask? kb ethical-form 'CxUniverse)))
      (testing "why explains it, deriving it from both dilemma sides"
        (let [tree  (tu/why-root kb ethical)
              antes (into #{} (mapcat #(map :handle (:because %))) (:support tree))]
          (is (:believed? tree))
          (is (= 2 (count (:support tree))) "one justification per side")
          (is (contains? antes pos) "derived from the pacifist side")
          (is (contains? antes neg) "derived from the non-pacifist side"))))))

;; ---- excluded conclusions and multiple dilemmas --------------------------

(deftest classify-local-excludes-a-conclusion-drawn-from-both-sides
  (with-redefs [solver/available? (constantly false)]
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [q (tu/tmp-pred) r (tu/tmp-pred) pac (tu/tmp-pred) weird (tu/tmp-pred) n (tu/tmp-ind)]
        (v/assert kb (tu/default-rule [(list q '?x)] (list pac '?x))             'CxUniverse)
        (v/assert kb (tu/default-rule [(list r '?x)] (list 'not (list pac '?x))) 'CxUniverse)
        (v/assert kb (bare-rule [(list pac '?x) (list 'not (list pac '?x))] (list weird '?x)) 'CxUniverse)
        (v/assert kb (list q n) 'CxUniverse)
        (v/assert kb (list r n) 'CxUniverse)
        (let [w-form (list weird n) w (v/handle-of kb w-form 'CxUniverse)
              cls    (label/classify-local kb)]
          (testing "it is believed — base belief holds both dilemma sides at once"
            (is (v/believed? kb w)))
          (testing "yet it is excluded, not merely credulous"
            (is (contains? (:false cls) w))
            (is (not (contains? (:supportable cls) w))))
          (testing "so the prover reports neither brave nor cautious"
            (is (not (v/ask? kb (list 'bravely    w-form) 'CxUniverse)))
            (is (not (v/ask? kb (list 'cautiously w-form) 'CxUniverse)))))))))

(defn- three-way-rebuttal
  "Three defaults where `b` rebuts BOTH `a` and `c` (and each rebuts `b`).  Defeating `b`
  alone resolves both dilemmas at cost one, so `a` and `c` hold in every optimal resolution
  and `b` in none — a joint outcome a per-dilemma reading cannot see, since dropping `a`
  resolves `a`'s dilemma at the same nominal cost as dropping `b`.  The dilemmas are coupled
  through the derivation graph, so classify-local enumerates them as one cluster."
  [kb]
  (let [pa (tu/tmp-pred) pb (tu/tmp-pred) pc (tu/tmp-pred) x (tu/tmp-ind)]
    (doseq [[p q] [[pa pb] [pb pa] [pc pb] [pb pc]]]
      (v/assert kb (tu/default-rule [(list p x)] (list 'not (list q x))) 'CxUniverse))
    (v/assert kb (list pa x) 'CxUniverse)
    (v/assert kb (list pb x) 'CxUniverse)
    (v/assert kb (list pc x) 'CxUniverse)
    {:a-form (list pa x) :b-form (list pb x) :c-form (list pc x)
     :a (v/handle-of kb (list pa x) 'CxUniverse)
     :b (v/handle-of kb (list pb x) 'CxUniverse)
     :c (v/handle-of kb (list pc x) 'CxUniverse)}))

(deftest classify-local-resolves-coupled-dilemmas
  (with-redefs [solver/available? (constantly false)]
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [a b c a-form b-form c-form]} (three-way-rebuttal kb)
            cls (label/classify-local kb)]
        (testing "the doubly-rebutted member holds in no optimal resolution"
          (is (contains? (:false cls) b))
          (is (not (v/ask? kb (list 'bravely    b-form) 'CxUniverse)))
          (is (not (v/ask? kb (list 'cautiously b-form) 'CxUniverse))))
        (testing "the two singly-rebutted members hold in every optimal resolution"
          (is (contains? (:true cls) a))
          (is (contains? (:true cls) c))
          (is (v/ask? kb (list 'cautiously a-form) 'CxUniverse))
          (is (v/ask? kb (list 'cautiously c-form) 'CxUniverse)))))))

(deftest the-backend-answers-coupled-dilemmas-as-the-bracket-does
  ;; the backend's optima over `three-way-rebuttal` call all six members `:supportable`
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [a-form b-form c-form]} (three-way-rebuttal kb)]
        (is (v/ask? kb (list 'cautiously a-form) 'CxUniverse))
        (is (v/ask? kb (list 'cautiously c-form) 'CxUniverse))
        (is (not (v/ask? kb (list 'bravely b-form) 'CxUniverse)))))))

(deftest a-member-is-refinable-only-past-the-cap-and-uncoupled
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [pos neg]} (nixon-diamond kb)
          {:keys [a b c]}   (three-way-rebuttal kb)]
      (testing "under the cap nothing is refinable"
        (is (empty? (:refinable (label/classify-local kb)))))
      (with-redefs [config/classify-max-cluster-members (constantly 1)]
        (let [refinable (:refinable (label/classify-local kb))]
          (testing "past it, a diamond's members are"
            (is (contains? refinable pos))
            (is (contains? refinable neg)))
          (testing "and a cluster whose members derive from one another is not"
            (is (not-any? refinable [a b c]))))))))

(deftest classify-local-classifies-independent-dilemmas-apart
  (with-redefs [solver/available? (constantly false)]
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [mk (fn []
                 (let [q (tu/tmp-pred) r (tu/tmp-pred) p (tu/tmp-pred) e (tu/tmp-pred) i (tu/tmp-ind)]
                   (v/assert kb (tu/default-rule [(list q '?x)] (list p '?x))             'CxUniverse)
                   (v/assert kb (tu/default-rule [(list r '?x)] (list 'not (list p '?x))) 'CxUniverse)
                   (v/assert kb (bare-rule [(list p '?x)]             (list e '?x)) 'CxUniverse)
                   (v/assert kb (bare-rule [(list 'not (list p '?x))] (list e '?x)) 'CxUniverse)
                   (v/assert kb (list q i) 'CxUniverse)
                   (v/assert kb (list r i) 'CxUniverse)
                   {:e-form (list e i) :e (v/handle-of kb (list e i) 'CxUniverse)
                    :p (v/handle-of kb (list p i) 'CxUniverse)}))
            d1  (mk) d2 (mk)
            cls (label/classify-local kb)]
        (testing "each diamond's both-sided conclusion is skeptical on its own"
          (is (contains? (:true cls) (:e d1)))
          (is (contains? (:true cls) (:e d2)))
          (is (v/ask? kb (list 'cautiously (:e-form d1)) 'CxUniverse))
          (is (v/ask? kb (list 'cautiously (:e-form d2)) 'CxUniverse)))
        (testing "each dilemma member stays credulous-only"
          (is (contains? (:supportable cls) (:p d1)))
          (is (contains? (:supportable cls) (:p d2))))))))

(deftest classify-local-agrees-with-the-backend-on-dilemma-members
  ;; the fixtures' members derive from none of each other, where a `Program` is exact;
  ;; `three-way-rebuttal` is left out, since its members derive from one another
  (when (solver/available?)
    (doseq [[title build] [["one diamond" extended-nixon]
                           ["two independent diamonds" #(do (extended-nixon %) (extended-nixon %))]]]
      (testing title
        (tu/with-neutral-kb [kb tu/fresh]
          (build kb)
          (let [program (label/dilemma-program kb)
                exact   (label/classify-program program)
                local   (label/classify-local kb)
                class   (fn [cls h] (some #(when (contains? (cls %) h) %) [:true :supportable :false]))
                shared  (filter #(class local %) (:assumptions program))]
            (is (seq shared) "the comparison covers at least one member")
            (doseq [h shared]
              (is (= (class exact h) (class local h))
                  (str "member " h " classifies differently")))))))))
