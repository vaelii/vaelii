;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inter-args-test
  "The homogeneity constraints — `(interArgs R T)` demands a `T` of every argument of an
  application once one argument is known to be a `T`, and `(interArgAndRest R n T)` makes
  the same demand of the positions from `n` onward.  `interArgs` is `interArgAndRest` at
  start 1, and CxCore's two forward rules derive each spelling from the other.

  Open-world as `interArg` is: the trigger must be positively established, and a target
  is convicted only when the KB places it in the hierarchy outside `T`.  An application
  whose arguments all lie outside `T` is unconstrained.  The refusal is `interArg`'s
  `:inter-arg-type`."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

;; CxCore's vocabulary, since the two forward rules relating the spellings are CxCore's.
;; A KB per test, because the restart tests open a second KB over the same stores.
(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- check-message
  "The message of the first check violation `v/check` reports for a sentence, or nil.
  `v/check` runs the checks `assert` runs and stores nothing, so the message is read
  without the dedup a second identical assert would hit."
  [kb sentence context]
  (:message (first (v/check kb sentence context))))

(defn- world
  "A `variable_arity_predicate` with an `arityMin` of 2, the types `animal` and `plant`
  under `thing` with `dog` under `animal`, and five individuals: three dogs and two
  plants.  Returns `{:rel :animal :dog :plant :dogs [A B C] :plants [P Q]}`."
  [kb]
  (let [rel (tu/tmp-pred) animal (tu/tmp-type) dog (tu/tmp-type) plant (tu/tmp-type)
        dogs   [(tu/tmp-ind) (tu/tmp-ind) (tu/tmp-ind)]
        plants [(tu/tmp-ind) (tu/tmp-ind)]]
    (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'genl plant 'thing) 'CxUniverse)
    (v/assert kb (list 'variable_arity_predicate rel) 'CxUniverse)
    (v/assert kb (list 'arityMin rel 2) 'CxUniverse)
    (doseq [d dogs] (v/assert kb (list dog d) 'CxUniverse))
    (doseq [p plants] (v/assert kb (list plant p) 'CxUniverse))
    {:rel rel :animal animal :dog dog :plant plant :dogs dogs :plants plants}))

;; ---- interArgs: every position ---------------------------------------------

(tu/deftest-kb interArgs-convicts-a-mixed-application-at-two-three-and-high-arity
  (let [{:keys [rel animal dogs plants]} (world kb)
        [a b c] dogs [p q] plants]
    (v/assert kb (list 'interArgs rel animal) 'CxUniverse)
    (testing "a known animal beside a known plant is refused at every length"
      (is (= :inter-arg-type (ex-type #(v/assert kb (list rel a p) 'CxUniverse))))
      (is (= :inter-arg-type (ex-type #(v/assert kb (list rel a b p) 'CxUniverse))))
      (is (= :inter-arg-type (ex-type #(v/assert kb (list rel a b c a p) 'CxUniverse)))))
    (testing "the trigger may sit after the target"
      (is (= :inter-arg-type (ex-type #(v/assert kb (list rel p q a) 'CxUniverse)))))
    (testing "an application of animals alone stores at every length"
      (is (v/assert kb (list rel a b) 'CxUniverse))
      (is (v/assert kb (list rel a b c) 'CxUniverse))
      (is (v/assert kb (list rel a b c b a) 'CxUniverse)))
    (testing "an application of non-animals alone is unconstrained"
      (is (v/assert kb (list rel p q) 'CxUniverse))
      (is (v/assert kb (list rel p q p q) 'CxUniverse)))))

(tu/deftest-kb the-refusal-names-the-trigger-and-the-target
  (let [{:keys [rel animal plant dogs plants]} (world kb)
        [a b] dogs [p] plants]
    (v/assert kb (list 'interArgs rel animal) 'CxUniverse)
    (let [problem (first (v/check kb (list rel a b p) 'CxUniverse))]
      (is (= :inter-arg-type (:type problem)))
      (is (= [p animal 3] ((juxt :arg :expected :position) problem)))
      (is (= [a animal 1] ((juxt :trigger :trigger-type :trigger-position) problem))
          "the first trigger in position order, a choice keyed on the sentence")
      (is (= (str "arg constraint: " p " must be a " animal " (interArgs, position 3 of "
                  rel ", because position 1 is a " animal ")")
             (:message problem))))
    (is plant)))

(tu/deftest-kb interArgs-is-open-world-on-both-sides
  (let [{:keys [rel animal dogs plants]} (world kb)
        [a] dogs [p] plants
        unknown (tu/tmp-ind)]
    (v/assert kb (list 'interArgs rel animal) 'CxUniverse)
    (testing "an argument the KB has not typed is no target"
      (is (v/assert kb (list rel a unknown) 'CxUniverse)))
    (testing "and no trigger: beside a plant it does not fire the constraint"
      (is (v/assert kb (list rel unknown p) 'CxUniverse)))
    (testing "a value is neither trigger nor target, the reading interArg gives both sides"
      (is (v/assert kb (list rel a "notTyped") 'CxUniverse)))))

;; ---- interArgAndRest: the suffix from a start ------------------------------

(tu/deftest-kb interArgAndRest-leaves-the-prefix-free
  (let [{:keys [rel animal dogs plants]} (world kb)
        [a b] dogs [p q] plants]
    (v/assert kb (list 'interArgAndRest rel 2 animal) 'CxUniverse)
    (testing "position 1 is below the start: a plant there beside animals stores"
      (is (v/assert kb (list rel p a b) 'CxUniverse)))
    (testing "and an animal there triggers nothing in the suffix"
      (is (v/assert kb (list rel a p q) 'CxUniverse)))
    (testing "a mixed suffix is refused, whatever sits at position 1"
      (is (= :inter-arg-type (ex-type #(v/assert kb (list rel p a q) 'CxUniverse))))
      (is (= :inter-arg-type (ex-type #(v/assert kb (list rel a b p) 'CxUniverse))))
      (is (= :inter-arg-type (ex-type #(v/assert kb (list rel p b a b a q) 'CxUniverse)))
          "to the actual end of a long application"))
    (testing "the message names the start"
      (is (re-find (re-pattern (str "\\(interArgAndRest from 2, position 2 of " rel
                                    ", because position 3 is a " animal "\\)"))
                   (check-message kb (list rel b p a) 'CxUniverse))))))

;; ---- a fixed-arity relation ------------------------------------------------

(tu/deftest-kb a-fixed-arity-relation-keeps-its-arity
  (tu/with-terms [rel animal plant A B P]
    (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl plant 'thing) 'CxUniverse)
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'interArgs rel animal) 'CxUniverse)
    (v/assert kb (list animal A) 'CxUniverse)
    (v/assert kb (list animal B) 'CxUniverse)
    (v/assert kb (list plant P) 'CxUniverse)
    (testing "within the arity the homogeneity constraint binds"
      (is (v/assert kb (list rel A B) 'CxUniverse))
      (is (= :inter-arg-type (ex-type #(v/assert kb (list rel A P) 'CxUniverse)))))
    (testing "and a third argument is still an arity refusal"
      (is (= :arity (ex-type #(v/assert kb (list rel A B A) 'CxUniverse)))))))

;; ---- the sugar -------------------------------------------------------------

(tu/deftest-kb interArgs-and-interArgAndRest-at-one-derive-each-other
  (let [{:keys [rel animal]} (world kb)
        rel2 (tu/tmp-pred)]
    (v/assert kb (list 'binary_predicate rel2) 'CxUniverse)
    (v/assert kb (list 'interArgs rel animal) 'CxUniverse)
    (v/assert kb (list 'interArgAndRest rel2 1 animal) 'CxUniverse)
    (testing "the stated interArgs has a stored interArgAndRest twin"
      (is (seq (v/sentexes-matching kb (list 'interArgAndRest rel 1 animal) 'CxUniverse))))
    (testing "the stated interArgAndRest at 1 has a stored interArgs twin"
      (is (seq (v/sentexes-matching kb (list 'interArgs rel2 animal) 'CxUniverse))))
    (testing "a start past 1 has no interArgs twin"
      (let [rel3 (tu/tmp-pred)]
        (v/assert kb (list 'binary_predicate rel3) 'CxUniverse)
        (v/assert kb (list 'interArgAndRest rel3 2 animal) 'CxUniverse)
        (is (empty? (v/sentexes-matching kb (list 'interArgs rel3 '?t) 'CxUniverse)))))))

(tu/deftest-kb either-spelling-refuses-in-the-same-words
  (let [{:keys [rel animal dogs plants]} (world kb)
        [a] dogs [p] plants
        mixed (list rel a p)
        refusal-under (fn [decl]
                        (let [h (v/assert kb decl 'CxUniverse)
                              r (v/check kb mixed 'CxUniverse)]
                          (v/retract! kb h)
                          r))
        by-sugar (refusal-under (list 'interArgs rel animal))
        by-start (refusal-under (list 'interArgAndRest rel 1 animal))]
    (is (= :inter-arg-type (:type (first by-sugar))))
    (is (= (mapv #(select-keys % [:type :message :arg :expected :position
                                  :trigger :trigger-type :trigger-position])
                 by-sugar)
           (mapv #(select-keys % [:type :message :arg :expected :position
                                  :trigger :trigger-type :trigger-position])
                 by-start))
        "the refusal is the same whichever spelling was stated")
    (testing "retracting the stated spelling takes its twin with it"
      (is (v/assert kb mixed 'CxUniverse))
      (is (false? (v/has-prop? kb :declares-inter-args-isa rel)))
      (is (false? (v/has-prop? kb :declares-inter-arg-and-rest-isa rel))))))

(tu/deftest-kb retracting-either-stated-spelling-collapses-the-pair
  ;; The two forward rules derive each spelling from the other, so each twin is justified
  ;; by the other as well as by what was stated.  Retracting the stated one has to take
  ;; both: a cycle the JTMS read as support would leave both believed with nothing stated.
  (let [{:keys [rel animal]} (world kb)]
    (doseq [[label stated twin] [["interArgs stated" (list 'interArgs rel animal)
                                  (list 'interArgAndRest rel 1 animal)]
                                 ["interArgAndRest stated" (list 'interArgAndRest rel 1 animal)
                                  (list 'interArgs rel animal)]]]
      (let [h (v/assert kb stated 'CxUniverse)]
        (is (and (v/ask? kb stated 'CxUniverse) (v/ask? kb twin 'CxUniverse))
            (str label ": both spellings are believed"))
        (v/retract! kb h)
        (is (not (or (v/ask? kb stated 'CxUniverse) (v/ask? kb twin 'CxUniverse)))
            (str label ", then retracted: neither spelling is believed"))
        (is (not (or (v/has-prop? kb :declares-inter-args-isa rel)
                     (v/has-prop? kb :declares-inter-arg-and-rest-isa rel)))
            (str label ", then retracted: neither mark stays"))))))

(defn- restarted
  "A process restart: a second KB over the same stores, whose in-memory taxonomy and
  JTMS are rebuilt from the records alone."
  []
  (doto (tu/test-kb) (v/recover)))

(tu/deftest-kb a-restart-reads-the-same-constraint-back
  (let [{:keys [rel animal dogs plants]} (world kb)
        [a] dogs [p] plants
        mixed (list rel a p)
        h (v/assert kb (list 'interArgs rel animal) 'CxUniverse)
        live (first (v/check kb mixed 'CxUniverse))]
    (testing "with the declaration stated, the restarted KB holds both spellings and refuses alike"
      (let [back (restarted)]
        (is (v/ask? back (list 'interArgAndRest rel 1 animal) 'CxUniverse))
        (is (v/has-prop? back :declares-inter-args-isa rel))
        (is (v/has-prop? back :declares-inter-arg-and-rest-isa rel))
        (is (= (:message live) (:message (first (v/check back mixed 'CxUniverse)))))))
    (v/retract! kb h)
    (testing "with it retracted, the restarted KB holds neither spelling and admits the application"
      (let [back (restarted)]
        (is (not (v/ask? back (list 'interArgs rel animal) 'CxUniverse)))
        (is (not (v/ask? back (list 'interArgAndRest rel 1 animal) 'CxUniverse)))
        (is (empty? (v/check back mixed 'CxUniverse)))))))

;; A stated declaration and its derived twin are one constraint.  The check reads both
;; spellings, so the reader is held here to merging them: were it not, the twin would
;; still refuse once (the first violation is the only one reported), and nothing at the
;; entry point would show the two being read as two.
(deftest a-declaration-and-its-twin-read-as-one-entry
  (let [decls (fn [kind]
                (case kind
                  interArgs       [[1 '{?type animal} {:sentence '(interArgs rel animal)}]]
                  interArgAndRest [[2 '{?start 1 ?type animal}
                                    {:sentence '(interArgAndRest rel 1 animal)}]
                                   [3 '{?start 2 ?type plant}
                                    {:sentence '(interArgAndRest rel 2 plant)}]
                                   [4 '{?start 0 ?type plant}
                                    {:sentence '(interArgAndRest rel 0 plant)}]]))]
    (is (= '[[1 animal rel] [2 plant rel]]
           (#'checks/homogeneity-declarations decls))
        "the twin pair is one entry, a later start is its own, and a start of 0 is dropped")))

;; ---- descent down the predicate hierarchy ----------------------------------

(tu/deftest-kb a-declaration-on-a-super-predicate-binds-a-sub
  (let [{super :rel :keys [animal dogs plants]} (world kb)
        [a] dogs [p] plants
        sub (tu/tmp-pred)]
    (v/assert kb (list 'interArgs super animal) 'CxUniverse)
    (v/assert kb (list 'variable_arity_predicate sub) 'CxUniverse)
    (v/assert kb (list 'genl sub super) 'CxUniverse)
    (is (= :inter-arg-type (ex-type #(v/assert kb (list sub a p) 'CxUniverse))))
    (is (re-find (re-pattern (str "declared of " super))
                 (check-message kb (list sub a p) 'CxUniverse)))))

;; ---- the query surface -----------------------------------------------------

(tu/deftest-kb the-type-is-answered-as-stated-and-the-predicate-descends
  (let [{:keys [rel animal dog]} (world kb)
        sub (tu/tmp-pred)]
    (v/assert kb (list 'variable_arity_predicate sub) 'CxUniverse)
    (v/assert kb (list 'genl sub rel) 'CxUniverse)
    (v/assert kb (list 'interArgs rel animal) 'CxUniverse)
    (v/assert kb (list 'interArgAndRest rel 2 animal) 'CxUniverse)
    (testing "the stated declarations answer themselves"
      (is (true? (v/ask? kb (list 'interArgs rel animal) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'interArgAndRest rel 2 animal) 'CxUniverse))))
    (testing "a sub-predicate is answered from its super's declaration"
      (is (true? (v/ask? kb (list 'interArgs sub animal) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'interArgAndRest sub 2 animal) 'CxUniverse))))
    (testing "the type generalizes neither down nor up genl"
      (is (not (v/ask? kb (list 'interArgs rel dog) 'CxUniverse)))
      (is (not (v/ask? kb (list 'interArgs rel 'thing) 'CxUniverse)))
      (is (not (v/ask? kb (list 'interArgAndRest rel 2 dog) 'CxUniverse))))
    (testing "and the start matches exactly"
      (is (not (v/ask? kb (list 'interArgAndRest rel 3 animal) 'CxUniverse))))))

;; ---- the declaration's own well-formedness ---------------------------------

(tu/deftest-kb the-declaration-is-well-formedness-checked
  (let [rel (tu/tmp-pred)]
    (testing "the start is a positive integer"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'interArgAndRest rel 0 'thing) 'CxUniverse))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'interArgAndRest rel -1 'thing) 'CxUniverse))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'interArgAndRest rel 'notAnInt 'thing) 'CxUniverse)))))
    (testing "the type is a type, not an individual"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'interArgs rel (tu/tmp-ind)) 'CxUniverse))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'interArgAndRest rel 2 (tu/tmp-ind)) 'CxUniverse)))))
    (testing "the subject is a relation, not a number"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'interArgs 5 'thing) 'CxUniverse)))))
    (testing "the message names the form"
      (is (re-find #"interArgAndRest start position must be a positive integer"
                   (check-message kb (list 'interArgAndRest rel 0 'thing) 'CxUniverse))))))

;; ---- arrival order ---------------------------------------------------------

(tu/deftest-kb every-order-of-the-ingredients-before-the-fact-refuses-alike
  ;; The declaration and the two memberships the refusal reads, in all six orders, then
  ;; the application.  Each order refuses with the same words, relation and terms apart.
  (let [messages
        (vec
         (for [order '[[:decl :trigger :target] [:decl :target :trigger]
                       [:trigger :decl :target] [:trigger :target :decl]
                       [:target :decl :trigger] [:target :trigger :decl]]]
           (tu/with-terms [rel animal plant A P]
             (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
             (v/assert kb (list 'genl plant 'thing) 'CxUniverse)
             (v/assert kb (list 'variable_arity_predicate rel) 'CxUniverse)
             (doseq [step order]
               (v/assert kb (case step
                              :decl    (list 'interArgs rel animal)
                              :trigger (list animal A)
                              :target  (list plant P))
                         'CxUniverse))
             (let [problem (first (v/check kb (list rel A P) 'CxUniverse))]
               [(:type problem)
                (-> (:message problem)
                    (str/replace (str rel) "R") (str/replace (str animal) "T")
                    (str/replace (str A) "A") (str/replace (str P) "P"))]))))]
    (is (= 6 (count messages)))
    (is (= #{[:inter-arg-type
              "arg constraint: P must be a T (interArgs, position 2 of R, because position 1 is a T)"]}
           (set messages)))))

;; ---- the derivation path ---------------------------------------------------

(tu/deftest-kb a-derived-mixed-application-is-recorded-not-thrown
  (let [{:keys [rel animal dogs plants]} (world kb)
        [a] dogs [p] plants
        trigger (tu/tmp-pred)]
    (v/assert kb (list 'interArgs rel animal) 'CxUniverse)
    (v/assert kb (list 'binary_predicate trigger) 'CxUniverse)
    (v/clear-violations! kb)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list trigger '?x '?y) (list rel '?x '?y)))
              'CxUniverse)
    (v/assert kb (list trigger a p) 'CxUniverse)
    (is (some #(= :inter-arg-type (:violation %)) (v/violations kb))
        "the conclusion is dropped into the ledger rather than aborting the fixpoint")
    (is (empty? (v/sentexes-matching kb (list rel a p) 'CxUniverse)))))
