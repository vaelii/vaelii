;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.generate-test
  "The synthetic KB generator: that a plan is a function of its parameters, that what it
  generates is well-formed by the naming invariants, and that loading it produces the
  shape the numbers asked for — with nothing dropped."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.io.generate :as gen]
            [vaelii.impl.naming :as nm]
            [vaelii.test-util :as tu]))

(def ^:private small
  "A KB small enough to assert about exhaustively, with every knob off its default so a
  parameter that is silently ignored shows up as a wrong count."
  {:types 12 :branching 3 :individuals 20 :predicates 9 :facts 40 :rules 8
   :forward 50 :defeasible 25 :antecedents 2 :layers 3 :contexts 2 :seed 5})

(deftest a-plan-with-fewer-predicates-than-layers-still-draws-every-rule
  ;; a band past the vocabulary is dropped rather than emitted empty: predicates 2
  ;; under layers 3 otherwise puts `(nth [] …)` inside the lazy rule draw, and the
  ;; throw lands mid-load, after the vocabulary has already been asserted
  (doseq [[preds layers] [[2 3] [4 6] [2 8]]]
    (let [p (gen/plan (assoc small :predicates preds :layers layers :rules 20))]
      (is (= 20 (count (doall (:rules p))))
          (str "every rule drawn at predicates " preds " layers " layers))
      (is (every? (comp some? first :consequent) (:rules p))
          "and every consequent names a predicate"))))

;; ---- the plan is a function of the parameters ---------------------------

(deftest plan-is-deterministic-in-its-seed
  (testing "the same parameters describe the same KB, every time"
    (let [a (gen/plan small)
          b (gen/plan small)]
      (is (= (vec (:facts a)) (vec (:facts b))))
      (is (= (vec (:rules a)) (vec (:rules b))))
      (is (= (vec (:memberships a)) (vec (:memberships b))))))
  (testing "a different seed describes a different one"
    (is (not= (vec (:facts (gen/plan small)))
              (vec (:facts (gen/plan (assoc small :seed 6))))))))

(deftest a-plan-is-the-same-whatever-order-its-streams-are-realized-in
  ;; The three seqs are lazy and *whoever holds the plan* decides the order they are
  ;; realized in: `load-into` takes memberships, then rules, then facts; a reader of the
  ;; map takes whichever it asks for first.  Drawn from one shared `Random` each stream's
  ;; values are a function of that order, so "the same numbers describe the same KB"
  ;; would hold only between two callers that happened to read them the same way — and
  ;; the corpus `load-into` asserts would not be the one `plan` was inspected as.  The
  ;; test above cannot see it, because it realizes both plans in one order.
  (let [a  (gen/plan small)
        b  (gen/plan small)
        ;; a, read facts-first; b, in `load-into`'s order
        af (vec (:facts a))
        ar (vec (:rules a))
        am (vec (:memberships a))
        bm (vec (:memberships b))
        br (vec (:rules b))
        bf (vec (:facts b))]
    (is (= am bm) "memberships")
    (is (= ar br) "rules")
    (is (= af bf) "facts")))

(deftest plan-counts-are-what-was-asked-for
  (let [{:keys [genls memberships facts rules units context-edges]} (gen/plan small)]
    (is (= (:types small) (count genls)))
    (is (= (:individuals small) (count memberships)))
    (is (= (:facts small) (count facts)))
    (is (= (:rules small) (count rules)))
    (testing "the context chain is one edge longer than the context list — the schema
              context's own edge under CxCore, which no band names"
      (is (= (inc (:contexts small)) (count context-edges))))
    (testing "units is the assertion count a progress bar divides by, and it counts the
              *edges* rather than the contexts, which is what `load-into` asserts"
      (is (= units (+ (count context-edges) (:types small) (:individuals small)
                      (:facts small) (:rules small)))))))

(deftest generated-names-satisfy-the-naming-invariants
  (let [{:keys [genls memberships facts rules context-edges]} (gen/plan small)]
    (testing "types are snake_case and used at arity 1"
      (doseq [[_ sub _] genls] (is (nm/type-symbol? sub)))
      (doseq [[s _] memberships]
        (is (nm/type-symbol? (nm/functor s)))
        (is (= 1 (nm/arity s)))))
    (testing "individuals are CapitalCamelCase, predicates camelCase"
      (doseq [[s _] (take 20 facts)]
        (is (nm/predicate? (nm/functor s)))
        (is (every? nm/individual? (nm/args s)))))
    (testing "contexts start with Cx"
      (doseq [[_ sub super] context-edges]
        (is (nm/context? sub))
        (is (nm/context? super))))
    (testing "no literal of a rule breaks a naming invariant"
      (doseq [r rules]
        (is (empty? (nm/problems (list 'implies (cons 'and (:antecedents r))
                                       (:consequent r))
                                 'CxGenerated)))))))

(deftest rules-are-range-restricted-and-stratified
  (let [{:keys [rules]} (gen/plan (assoc small :rules 200))]
    (testing "every consequent variable is bound by an antecedent"
      (doseq [{:keys [antecedents consequent]} rules]
        (let [bound (into #{} (mapcat #(filter symbol? (nm/args %))) antecedents)]
          (is (every? bound (filter #(re-find #"^\?" (name %)) (nm/args consequent)))))))
    (testing "a rule concludes strictly above the layer it reads from, so the rule set
              is acyclic and forward chaining terminates"
      (let [layer-of (fn [p] (some (fn [[k ps]] (when (ps p) k))
                                   (map-indexed vector
                                                (map set (#'gen/bands
                                                          (max 2 (:predicates small))
                                                          (:layers small))))))]
        (doseq [{:keys [antecedents consequent layer]} rules]
          (is (= layer (layer-of (nm/functor consequent))))
          (doseq [a antecedents]
            (is (< (layer-of (nm/functor a)) layer))))))))

;; ---- loading one ---------------------------------------------------------

(deftest loading-a-generated-kb-produces-the-shape-asked-for
  (tu/with-cleared-kb [kb tu/fresh]
    (let [events (atom [])
          r (gen/load-into kb small {:on-progress #(swap! events conj %)})
          phases (mapv :phase @events)]
      (testing "the summary reports what landed"
        (is (pos? (:stored r)))
        (is (= (merge gen/defaults small) (:params r))))
      (testing "progress runs through the phases in load order and ends at :done"
        (is (= [:vocabulary :contexts :types :individuals :rules :facts :done]
               (vec (distinct phases)))))
      (testing "and the phases count exactly the units the plan promised, so the bar
                reaches its end rather than overrunning it"
        (let [final (last @events)]
          (is (= (:units r) (:total final)))
          (is (= (:total final) (:done final)))))
      (testing "the type hierarchy is rooted at thing"
        (is (contains? (v/genls kb 'gen_type_11) 'thing))
        (is (contains? (v/specs kb 'thing) 'gen_type_0)))
      (testing "the fact contexts are a chain under the schema context, so any two facts
                a rule joins have a common descendant to put its conclusion in"
        (is (v/sees? kb 'CxGenBand1 'CxGenBand0))
        (is (v/sees? kb 'CxGenBand0 'CxGenerated)))
      (testing "the rules are there, in the mix the plan drew — the load spells direction
                and defeasibility into the sentence and both canonicalize back out"
        ;; Counted against the plan's **distinct sentences** rather than its rule count: a
        ;; draw can repeat a rule, and two identical sentences are one sentex.  Direction
        ;; and defeasibility ride the sentence (`set/forwardRule`, `set/defaultRule`), so
        ;; the survivor of a repeat carries the same pair and the mix follows exactly.
        (let [rules  (filter :antecedent (v/sentexes-in-context kb 'CxGenerated))
              wanted (vals (into {} (map (juxt #(#'gen/rule-sentence %) identity))
                                 (:rules (gen/plan small))))]
          (is (= (count wanted) (count rules)))
          (is (= (count (filter #(= :forward (:direction %)) wanted))
                 (count (filter #(= :forward (:direction %)) rules))))
          (is (= (count (filter :defeasible? wanted))
                 (count (filter :defeasible rules)))))))))

(deftest direction-and-defeasibility-are-independent-draws
  ;; Read off one rule index they were two thresholds on the same number, so at any
  ;; settings where `:defeasible` ≤ `:forward` every defeasible rule was also a forward
  ;; one — and no settings at all produced a defeasible *backward* rule, a shape the
  ;; corpus therefore could not exercise however the knobs were turned.
  (let [rules (:rules (gen/plan (assoc small :rules 2000 :forward 50 :defeasible 50)))
        cell  (fn [def? fwd?]
                (count (filter #(and (= def? (boolean (:defeasible? %)))
                                     (= fwd? (= :forward (:direction %))))
                               rules)))]
    (testing "all four combinations of the two are drawn"
      (doseq [[def? fwd?] [[true true] [true false] [false true] [false false]]]
        (is (pos? (cell def? fwd?))
            (str "defeasible? " def? " forward? " fwd?))))
    (testing "and each share is near the percentage that was asked for"
      (is (< 800 (count (filter #(= :forward (:direction %)) rules)) 1200))
      (is (< 800 (count (filter :defeasible? rules)) 1200)))))

(deftest a-fact-repeated-in-a-second-context-is-a-second-sentex
  ;; The load dedups so `bulk-assert-facts!`'s precondition holds, and that precondition
  ;; is "no two the same sentence **in the same context**".  Keyed on the sentence alone
  ;; the dedup drops every repeat past the first, so `:contexts` spreads the facts over
  ;; more contexts without the KB holding any more of them — a corpus short of the number
  ;; that was asked for, with nothing in the summary to say so.
  (tu/with-cleared-kb [kb tu/fresh]
    ;; three individuals over two base predicates is an 18-sentence space, so 200 draws
    ;; repeat a sentence in both contexts many times over
    (let [params (assoc small :facts 200 :individuals 3 :predicates 4 :layers 2
                        :rules 0 :contexts 2)
          dup    (->> (group-by first (:facts (gen/plan params)))
                      (keep (fn [[s es]]
                              (let [cs (distinct (map second es))]
                                (when (< 1 (count cs)) [s (vec cs)]))))
                      first)]
      (is (some? dup) "the corpus repeats a sentence across the two contexts")
      (gen/load-into kb params)
      (when-let [[s cs] dup]
        (let [hs (mapv #(v/handle-of kb s %) cs)]
          (is (every? some? hs) "every context that holds it has its own sentex")
          (is (apply distinct? hs) "and they are distinct handles"))))))

(deftest ^:slow a-generated-kb-derives-cleanly
  (testing "chaining over a generated corpus drops nothing: every firing has a placement
            context, and no definitional check refuses a conclusion"
    (tu/with-cleared-kb [kb tu/fresh]
      ;; individuals ≈ facts keeps the joins sparse, which is what a real corpus looks
      ;; like; a handful of individuals shared by every fact is a cross product, and the
      ;; depth bound (not this test) is what keeps *that* case finite
      (let [r (gen/load-into kb (assoc small :individuals 200 :facts 200 :rules 20
                                       :forward 100 :chain? true))]
        (is (pos? (:derived r)))
        (is (empty? (v/violations kb)))
        (is (empty? (v/conflicts kb)))))))

(deftest a-small-generated-kb-derives-cleanly
  ;; The `^:slow` test above at under a third of its corpus, so `:default` chains a
  ;; generated KB and checks it drops nothing.  Sixty facts over thirty individuals is
  ;; dense enough that the forty forward rules derive; at a tenth of the slow test's
  ;; corpus they derive nothing, and `(pos? (:derived r))` fails.
  (tu/with-cleared-kb [kb tu/fresh]
    (let [r (gen/load-into kb (assoc small :individuals 30 :facts 60 :rules 8
                                     :forward 40 :chain? true))]
      (is (pos? (:derived r)))
      (is (empty? (v/violations kb)))
      (is (empty? (v/conflicts kb))))))

(deftest the-progress-callback-can-cancel-a-load
  (testing "a callback that throws stops the load where it stands — the extension point the catalog
            cancels on"
    (tu/with-cleared-kb [kb tu/fresh]
      (let [seen (atom 0)]
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"enough"
             (gen/load-into kb (assoc small :facts 100000)
                            {:on-progress (fn [_]
                                            (when (< 3 (swap! seen inc))
                                              (throw (ex-info "enough" {}))))})))
        (testing "and what had landed before the throw is still there — a load is not a
                  transaction, and the catalog's unload is what cleans it up"
          (is (pos? (count (v/types kb)))))))))
