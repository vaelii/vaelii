;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.check-test
  "`check` / `check-edit` — `assert`'s own checks run for their answer rather than for
  their effect.  Two things have to hold of every case here: the `:type` is the one
  `assert` would have thrown, and **nothing is stored** — a check that wrote would be
  worse than useless to the caller asking whether it is safe to write."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(defn- kb-with-starter [] (doto (tu/fresh) (starter/load-into)))

(defn- types-of-check
  "The `:type` keywords `check` reports for a sentence, as a set."
  [kb sentence context]
  (into #{} (map :type) (v/check kb sentence context)))

(defn- assert-type
  "The `:type` `assert` actually throws for the same sentence, or nil when it stores."
  [kb sentence context]
  (try (v/assert kb sentence context) nil
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- the checks agree with assert, one type at a time -------------------

(deftest check-reports-the-type-assert-would-throw
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [dog cat Muffet TheContext]
      ;; the disjointness constrains where it is visible, so the asserting context
      ;; is wired below the declaring one
      (v/assert kb (list 'genlContext TheContext 'CoreContext) 'CoreContext)
      (v/assert kb (list 'genl dog 'animal) 'CoreContext)
      (v/assert kb (list 'genl cat 'animal) 'CoreContext)
      (v/assert kb (list 'disjoint dog cat) 'CoreContext)
      (v/assert kb (list dog Muffet) TheContext)
      (doseq [[label sentence context expected]
              [["a bad context"        (list dog Muffet) 'notacontext          :naming]
               ["a bad functor"        (list 'BadPred Muffet) TheContext       :naming]
               ["a variable in a fact" (list dog '?x) TheContext             :not-ground]
               ["genl over an individual" (list 'genl Muffet dog) TheContext   :not-well-formed]
               ["an unbound consequent variable"
                (list 'implies (list dog '?x) (list 'animal '?y)) TheContext :not-range-restricted]
               ;; the rule index is keyed by predicate, and a variable names none — so
               ;; `check` has to predict the refusal `assert` makes, or an editor
               ;; validating a metarule is told it will land when it will not
               ["a rule literal with a variable predicate"
                (list 'implies (list 'and (list dog '?x) (list 'transitive '?p))
                      (list '?p '?x '?x)) TheContext                          :not-indexable]
               ["a disjoint type membership" (list cat Muffet) TheContext      :disjoint]]]
        (testing label
          (is (= #{expected} (types-of-check kb sentence context)))
          (is (= expected (assert-type kb sentence context))
              "and it is the type assert throws for the same sentence"))))))

(deftest an-admissible-sentence-has-no-problems
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob TheContext]
      (is (= [] (v/check kb (list likesOf Alice Bob) TheContext)))
      (is (= [] (v/check kb (list 'implies (list likesOf '?x '?y) (list likesOf '?y '?x))
                         TheContext)))
      (testing "and asserting it does succeed"
        (is (some? (v/assert kb (list likesOf Alice Bob) TheContext)))))))

;; ---- nothing is stored --------------------------------------------------

(deftest check-stores-nothing-whatever-the-answer
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob newType TheContext]
      (doseq [sentence [(list likesOf Alice Bob)                ; admissible
                        (list likesOf Alice '?x)                ; not ground
                        (list 'genl newType 'animal)            ; a taxonomy edge
                        (list 'implies (list likesOf '?x '?y) (list likesOf '?y '?x))]]
        (v/check kb sentence TheContext))
      (testing "no sentex was created for any of them"
        (is (nil? (v/handle-of kb (list likesOf Alice Bob) TheContext)))
        (is (empty? (v/find-sentexes kb likesOf))))
      (testing "and the taxonomy edge the check considered did not reach the closure"
        (is (not (v/genl? kb newType 'animal)))))))

;; ---- naming reaches below the top level --------------------------------

(deftest naming-is-reported-for-every-literal-not-only-the-outermost
  ;; the outermost functor of a rule is `implies`, which is engine vocabulary — the
  ;; predicate the author named sits in the consequent, which is where generated
  ;; content lands
  (tu/with-neutral-kb [kb kb-with-starter]
    (doseq [[label sentence]
            [["a snake_case relation in a rule consequent"
              '(implies (penguin ?x) (lives_in ?x cold_place))]
             ["a snake_case relation asserted as a fact"
              '(lives_in penguin cold_place)]
             ["a snake_case relation between two types"
              '(disjoint_with penguin fish)]]]
      (testing label
        (is (= #{:naming} (types-of-check kb sentence 'WellContext)))
        (is (= :naming (assert-type kb sentence 'WellContext))
            "and it is the type assert throws for the same sentence")))
    (testing "a *unary* snake_case functor is a well-formed type name, however coined"
      ;; this check is about the shape of a name, not about whether the vocabulary
      ;; wants it — refusing an implausible type is a different question
      (is (= [] (v/check kb '(implies (penguin ?x) (has_black_and_white_feathers ?x))
                         'WellContext))))))

(deftest check-edit-carries-a-nested-naming-problem-per-entry
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob TheContext]
      (let [ps (v/check-edit kb {:add [[(list likesOf Alice Bob) TheContext]
                                       ['(implies (penguin ?x) (lives_in ?x cold_place))
                                        'WellContext]
                                       ['(disjoint_with penguin fish) 'WellContext]]})]
        (is (= [{:in :add :index 1 :type :naming}
                {:in :add :index 2 :type :naming}]
               (mapv #(select-keys % [:in :index :type]) ps)))
        (testing "and the message names the literal, its frame, and what to write"
          (let [m (:message (first ps))]
            (is (re-find #"rule consequent" m))
            (is (re-find #"lives_in" m))
            (is (re-find #"livesIn" m))))))))

;; ---- shape: the request itself, not the knowledge -----------------------

(deftest a-request-that-is-not-a-sentence-in-a-context-is-shaped-wrong
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [dog Muffet TheContext]
      (is (= #{:shape} (types-of-check kb (list dog Muffet) "TheContext")))
      (is (= #{:shape} (types-of-check kb 'dog TheContext)))
      ;; a non-map opts is an opts problem, not a shape one — the same
      ;; `:unknown-option` `assert` throws, since `shape-problems` runs its guard
      (is (= #{:unknown-option}
             (into #{} (map :type) (v/check kb (list dog Muffet) TheContext :nope)))))))

;; ---- the opts roster: admissible knowledge, inadmissible request ---------
;; These two are the request rather than the sentence, and neither is visible after the
;; fact: both store the sentence at a defeat class the caller did not ask for, and a
;; sentex carries no record of the class it was *meant* to have.  So `check` must answer
;; for them, and `assert` must refuse rather than fall back.

(deftest an-opts-key-assert-does-not-read-is-refused-not-defaulted
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob TheContext]
      (let [sentence (list likesOf Alice Bob)]
        (testing "a misspelt key would silently store a default where known-true was meant"
          (is (= #{:unknown-option} (into #{} (map :type)
                                          (v/check kb sentence TheContext {:strenth :monotonic}))))
          (is (= :unknown-option (try (v/assert kb sentence TheContext {:strenth :monotonic}) nil
                                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
        (testing "and the refusal names both the offending key and the roster"
          (let [d (try (v/assert kb sentence TheContext {:strenth :monotonic}) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
            (is (= [:strenth] (:unknown d)))
            (is (= (vec (sort v/assert-opt-keys)) (:options d)))))
        (testing "nothing was stored by either"
          (is (empty? (v/sentexes-matching kb sentence TheContext))))
        (testing "every key on the roster is still accepted"
          (is (empty? (v/check kb sentence TheContext
                               {:strength :monotonic :chain? false :max-depth 8
                                :creator "t" :provenance {:source :test}}))))))))

(deftest a-strength-outside-the-two-classes-is-refused
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob TheContext]
      (let [sentence (list likesOf Alice Bob)]
        (doseq [bad [0.7 :monotonicc nil "monotonic"]]
          (testing (str "strength " (pr-str bad))
            (is (= #{:unknown-option} (into #{} (map :type)
                                            (v/check kb sentence TheContext {:strength bad}))))
            (is (= :unknown-option (try (v/assert kb sentence TheContext {:strength bad}) nil
                                        (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))
        (is (empty? (v/sentexes-matching kb sentence TheContext)))
        (testing "both assertable classes still land"
          (is (some? (v/assert kb sentence TheContext {:strength :monotonic})))
          (is (= :monotonic (v/defeat-class kb (v/handle-of kb sentence TheContext)))))))))

(deftest assert-rule-holds-its-opts-to-the-same-roster
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [base derived TheContext]
      (let [antes [(list base '?x)] conseq (list derived '?x)]
        (is (= :unknown-option (try (v/assert-rule kb antes conseq TheContext {:dir :forward}) nil
                                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
        (testing ":direction itself is on the roster"
          (is (some? (v/assert-rule kb antes conseq TheContext {:direction :forward}))))))))

;; ---- stratification: the rule-set check runs too ------------------------

(deftest a-rule-closing-a-cycle-through-negation-is-reported-not-stored
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [base aP bP TheContext]
      ;; bP is concluded by a rule whose exception reads aP; a second rule concluding
      ;; aP from bP closes the cycle through that negation
      (v/assert kb (list 'exceptWhen (list aP '?x)
                         (list 'set/defaultRule
                               (list 'implies (list base '?x) (list bP '?x))))
                TheContext)
      (let [cyclic (list 'implies (list bP '?x) (list aP '?x))
            ps     (v/check kb cyclic TheContext)]
        (is (= #{:not-stratified} (into #{} (map :type) ps)))
        (testing "and the reported cycle is the one the refusal names"
          (is (seq (:cycle (first ps)))))
        (is (= :not-stratified (assert-type kb cyclic TheContext)))))))

;; ---- the batch form -----------------------------------------------------

(deftest check-edit-points-at-the-entry-that-is-wrong
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob TheContext]
      (let [h  (v/assert kb (list likesOf Alice Bob) TheContext)
            ps (v/check-edit kb {:add    [[(list likesOf Alice Bob) TheContext]
                                          [(list likesOf Alice '?x) TheContext]
                                          [:not-an-entry]]
                                 :remove [h 999999 :nope]})]
        (testing "the admissible add contributes nothing"
          (is (empty? (filter #(= 0 (:index %)) (filter #(= :add (:in %)) ps)))))
        (testing "each problem names where it came from"
          (is (= [{:in :add :index 1 :type :not-ground}
                  {:in :add :index 2 :type :shape}
                  {:in :remove :index 1 :type :unknown-handle}
                  {:in :remove :index 2 :type :bad-handle}]
                 (mapv #(select-keys % [:in :index :type]) ps))))
        (testing "and a stored handle is a fine removal"
          (is (empty? (filter #(and (= :remove (:in %)) (= 0 (:index %))) ps))))
        (testing "an empty batch has no problems"
          (is (= [] (v/check-edit kb {:add [] :remove []}))))))))

(deftest check-edit-judges-each-add-against-the-kb-as-it-stands
  ;; Nothing is stored, so each add is judged against the KB *before the batch*, not
  ;; against the KB the entries before it would have made.  That is the honest answer
  ;; for a dry run, and it differs from the sequential reading in **both** directions —
  ;; so both are pinned, because an assertion true under either reading says nothing
  ;; about which one `check-edit` implements.
  (tu/with-neutral-kb [kb kb-with-starter]
    (testing "an add admissible only *after* an earlier one landed is still reported"
      ;; sequentially the genl edge lands first and puts the kind under the constraint
      ;; type; as it stands the kind reaches `thing` and not the constraint, which is
      ;; the visible-evidence-in-the-wrong-place case argGenl convicts
      (tu/with-terms [relOf a_kind an_animal Rex TheContext]
        (v/assert kb (list 'genlContext TheContext 'CoreContext) 'CoreContext)
        (v/assert kb (list 'genl an_animal 'thing) 'CoreContext)
        (v/assert kb (list 'genl a_kind 'thing) 'CoreContext)
        (v/assert kb (list 'argGenl relOf 1 an_animal) 'CoreContext)
        (let [ps (v/check-edit kb {:add [[(list 'genl a_kind an_animal) TheContext]
                                         [(list relOf a_kind Rex) TheContext]]})]
          (is (= [{:in :add :index 1 :type :arg-genl}]
                 (mapv #(select-keys % [:in :index :type]) ps))
              "the second add was judged against a KB the first had already changed"))))
    (testing "and an add the KB as it stands admits is *not* reported for what an
              earlier one would have forbidden"
      ;; the mirror: sequentially the declaration binds the fact after it and the arity
      ;; check refuses; as it stands nothing is declared and open world admits it
      (tu/with-terms [pOf Thing TheContext]
        (let [ps (v/check-edit kb {:add [[(list 'binaryPredicate pOf) TheContext]
                                         [(list pOf Thing) TheContext]]})]
          (is (= [] ps)
              "the declaration in the same batch was read as though it had landed"))))
    (testing "and the open-world floor still holds: an untyped argument violates nothing"
      (tu/with-terms [newPred Thing TheContext]
        (is (= [] (v/check-edit kb {:add [[(list 'argIsa newPred 1 'animal) TheContext]
                                          [(list newPred Thing) TheContext]]})))))))

;; ---- which declaration a violation names: content, not arrival ----------

(deftest an-arg-type-violation-names-the-content-sorted-declaration
  ;; two visible argIsa declarations convict the same sentence, one per argument;
  ;; the single reported violation must name the content-sort winner in every
  ;; assertion order — `res/matches-visible` promises the answer *set*, so
  ;; enumeration order may not pick the declaration a refusal is about
  (doseq [flip? [false true]]
    (tu/with-neutral-kb [kb kb-with-starter]
      (tu/with-terms [relOf t_first t_second t_plain Muffet Alice TheContext]
        (v/assert kb (list 'genlContext TheContext 'CoreContext) 'CoreContext)
        (doseq [t [t_first t_second t_plain]]
          (v/assert kb (list 'genl t 'thing) 'CoreContext))
        (let [d1     (list 'argIsa relOf 1 t_first)
              d2     (list 'argIsa relOf 2 t_second)
              winner (first (sort-by pr-str [d1 d2]))]
          (doseq [d (if flip? [d2 d1] [d1 d2])]
            (v/assert kb d 'CoreContext))
          (v/assert kb (list t_plain Muffet) TheContext)
          (v/assert kb (list t_plain Alice) TheContext)
          (let [ps (v/check kb (list relOf Muffet Alice) TheContext)
                p  (first (filter #(= :arg-type (:type %)) ps))]
            (testing (str "assertion order " (if flip? "second first" "first second"))
              (is (some? p) "both declarations convict, so a violation is reported")
              (is (= (nth winner 2) (:position p)))
              (is (= (nth winner 3) (:expected p))))))))))

;; ---- ist and the wrappers dispatch the way assert does ------------------

(deftest check-follows-assert-into-ist-and-the-rule-wrappers
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice IstContext]
      (testing "(ist Ctx S) is checked as S in Ctx"
        (is (= #{:not-ground}
               (types-of-check kb (list 'ist IstContext (list likesOf Alice '?x)) 'UniverseContext))))
      (testing "a set/*Rule wrapper is checked as the rule it wraps"
        (is (= #{:not-range-restricted}
               (types-of-check kb (list 'set/forwardRule
                                        (list 'implies (list 'dog '?x) (list 'animal '?y)))
                               IstContext)))))))

(deftest an-ist-form-holds-exactly-three-elements
  ;; `(ist Ctx S)` is the form, and both `assert` and `check` read it by position — so a
  ;; wrong length has to be refused rather than indexed into.  Two elements reached
  ;; `(nth sentence 2)`; four asserted with the extra silently dropped, which is the
  ;; worse of the two because it stores something the caller did not write.
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [dog Muffet IstContext]
      (let [short-form (list 'ist IstContext)
            long-form  (list 'ist IstContext (list dog Muffet) 'junk)]
        (testing "check reports the shape rather than raising out of nth"
          (is (= #{:shape} (types-of-check kb short-form 'UniverseContext)))
          (is (= #{:shape} (types-of-check kb long-form 'UniverseContext))))
        (testing "and assert refuses both with the same :type"
          (doseq [form [short-form long-form]]
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (v/assert kb form 'UniverseContext))
                        (str (pr-str form) " is refused"))]
              (is (= :shape (:type (ex-data e)))))))
        (testing "and the over-long one stored nothing"
          (is (empty? (v/sentexes-matching kb (list dog '?x) IstContext))))))))

;; ---- assert-inert runs the same shape guards ----------------------------

(deftest assert-inert-refuses-the-shapes-assert-refuses
  ;; `assert-inert` skips the constraint / wff / chaining machinery on purpose — a
  ;; materialized head is already well-formed — but the shape guards are not machinery,
  ;; they are what keeps a non-sentence out of the store.  `nm/literals` of a
  ;; non-sequential sentence finds no literals, so a string or nil would pass the naming
  ;; check vacuously and store as an object no query can match.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet InertContext]
      (let [before (v/sentex-count kb)]
        (testing "a non-sequential sentence is :shape, as at assert"
          (doseq [bad ["(dog Muffet)" nil 42 {:a 1}]]
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (v/assert-inert kb bad InertContext))
                        (str (pr-str bad) " is refused"))]
              (is (= :shape (:type (ex-data e)))))))
        (testing "a non-symbol context is :shape, not :naming"
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (v/assert-inert kb (list dog Muffet) (str InertContext))))]
            (is (= :shape (:type (ex-data e))))))
        (testing "and nothing was stored by any refusal"
          (is (= before (v/sentex-count kb)))))
      (testing "a well-formed inert sentex still stores, unbelieved"
        (let [h (v/assert-inert kb (list dog Muffet) InertContext)]
          (is (nat-int? h))
          (is (not (v/in? kb h)) "inert means never a premise")
          (v/retract! kb h))))))
