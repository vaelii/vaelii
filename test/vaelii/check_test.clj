;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.check-test
  "`check` / `check-edit` — `assert`'s own checks run for their answer rather than for
  their effect.  Two things have to hold of every case here: the `:type` is the one
  `assert` would have thrown, and **nothing is stored** — a check that wrote would be
  worse than useless to the caller asking whether it is safe to write."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- kb-with-starter
  "A fresh starter KB per test — `check` and `assert` are compared on the same baseline
  and `assert-type` really does store, so the isolation is per-test rather than per
  namespace.  Restored from `tu/load-starter!`'s dump rather than re-asserted: this
  namespace builds one 23 times, and the two routes produce the same KB
  (`starter_copy_test`)."
  [] (doto (tu/empty-kb) (tu/load-starter!)))

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
    (tu/with-terms [dog cat Muffet CxThe]
      ;; the disjointness constrains where it is visible, so the asserting context
      ;; is wired below the declaring one
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl dog 'animal) 'CxUniverse)
      (v/assert kb (list 'genl cat 'animal) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (v/assert kb (list dog Muffet) CxThe)
      (doseq [[label sentence context expected]
              [["a bad context"        (list dog Muffet) 'notacontext          :naming]
               ["a bad functor"        (list 'BadPred Muffet) CxThe       :naming]
               ["a variable in a fact" (list dog '?x) CxThe             :not-ground]
               ["genl over an individual" (list 'genl Muffet dog) CxThe   :not-well-formed]
               ;; negation lives on facts: a rule under `not` would store a sentence
               ;; its own key cannot be computed from, so both entry points refuse it —
               ;; wrapped exactly as bare, since the wrappers peel before the test
               ["a negated rule"
                (list 'not (list 'implies (list dog '?x) (list 'animal '?x)))
                CxThe                                                     :not-well-formed]
               ["a negated wrapped rule"
                (list 'not (list 'set/defaultRule
                                 (list 'implies (list dog '?x) (list 'animal '?x))))
                CxThe                                                     :not-well-formed]
               ["an unbound consequent variable"
                (list 'implies (list dog '?x) (list 'animal '?y)) CxThe :not-range-restricted]
               ;; the rule index is keyed by predicate, and a variable in *antecedent*
               ;; functor position names none — so `check` has to predict the refusal
               ;; `assert` makes, or an editor validating a metarule is told it will land
               ;; when it will not.  (A variable *consequent* functor is allowed now, so
               ;; the variable has to sit in the antecedent for this to refuse.)
               ["a rule antecedent literal with a variable predicate"
                (list 'implies (list 'and (list '?p '?x '?y) (list 'transitive '?p))
                      (list '?p '?x '?x)) CxThe                          :not-indexable]
               ;; the operand of a wrapper or a `not` is a sentence, and a bare symbol
               ;; there is refused as a bare antecedent or consequent literal is
               ["a rule wrapper around a bare symbol"
                (list 'set/defaultRule Muffet) CxThe                       :not-well-formed]
               ["a negated bare symbol" (list 'not Muffet) CxThe          :not-well-formed]
               ;; a conjunct is a formula and a variable is a term: stored, the rule
               ;; fired forward as if the conjunct were absent and never fired backward
               ["a bare variable as an antecedent conjunct"
                (list 'implies (list 'and (list dog '?x) '?y) (list 'animal '?x))
                CxThe                                                     :not-well-formed]
               ["a bare variable under a negated antecedent"
                (list 'implies (list 'and (list dog '?x) (list 'not '?y)) (list 'animal '?x))
                CxThe                                                     :not-well-formed]
               ["a generator whose generated rule has a bare variable conjunct"
                (list 'set/forwardRule
                      (list 'implies (list dog '?x)
                            (list 'implies (list 'and (list cat '?z) '?y) (list dog '?z))))
                CxThe                                                     :not-well-formed]
               ["a bare variable as an exception conjunct"
                (list 'exceptWhen '?y (list 'implies (list dog '?x) (list 'animal '?x)))
                CxThe                                                     :not-well-formed]
               ["a rule wrapper around a bare variable"
                (list 'set/forwardRule '?y) CxThe                         :not-well-formed]
               ;; a consequent is a formula too: the derived sentence whose predicate a
               ;; firing binds is written (?pred . ?args)
               ["a bare variable as a consequent"
                (list 'implies (list dog '?s) '?s) CxThe                  :not-well-formed]
               ["a bare variable in a conjunctive consequent"
                (list 'implies (list dog '?s) (list 'and (list 'animal '?s) '?s))
                CxThe                                                     :not-well-formed]
               ["a bare variable under a head existential"
                (list 'implies (list dog '?s) (list 'exists '?y '?s))
                CxThe                                                     :not-well-formed]
               ["a bare variable under a negated consequent"
                (list 'implies (list dog '?s) (list 'not '?s)) CxThe      :not-well-formed]
               ["a generator whose generated rule has a bare variable consequent"
                (list 'set/forwardRule
                      (list 'implies (list dog '?x) (list 'implies (list cat '?z) '?z)))
                CxThe                                                     :not-well-formed]]]
        (testing label
          (is (= #{expected} (types-of-check kb sentence context)))
          (is (= expected (assert-type kb sentence context))
              "and it is the type assert throws for the same sentence"))))))

(deftest an-admissible-sentence-has-no-problems
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob CxThe]
      (is (= [] (v/check kb (list likesOf Alice Bob) CxThe)))
      (is (= [] (v/check kb (list 'implies (list likesOf '?x '?y) (list likesOf '?y '?x))
                         CxThe)))
      (testing "and asserting it does succeed"
        (is (some? (v/assert kb (list likesOf Alice Bob) CxThe)))))))

;; ---- nothing is stored --------------------------------------------------

(deftest check-stores-nothing-whatever-the-answer
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob newType CxThe]
      (doseq [sentence [(list likesOf Alice Bob)                ; admissible
                        (list likesOf Alice '?x)                ; not ground
                        (list 'genl newType 'animal)            ; a taxonomy edge
                        (list 'implies (list likesOf '?x '?y) (list likesOf '?y '?x))]]
        (v/check kb sentence CxThe))
      (testing "no sentex was created for any of them"
        (is (nil? (v/handle-of kb (list likesOf Alice Bob) CxThe)))
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
        (is (= #{:naming} (types-of-check kb sentence 'CxWell)))
        (is (= :naming (assert-type kb sentence 'CxWell))
            "and it is the type assert throws for the same sentence")))
    (testing "a *unary* snake_case functor is a well-formed type name, however coined"
      ;; this check is about the structure of a name, not about whether the vocabulary
      ;; wants it — refusing an implausible type is a different question
      (is (= [] (v/check kb '(implies (penguin ?x) (has_black_and_white_feathers ?x))
                         'CxWell))))))

(deftest check-edit-carries-a-nested-naming-problem-per-entry
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob CxThe]
      (let [ps (v/check-edit kb {:add [[(list likesOf Alice Bob) CxThe]
                                       ['(implies (penguin ?x) (lives_in ?x cold_place))
                                        'CxWell]
                                       ['(disjoint_with penguin fish) 'CxWell]]})]
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
    (tu/with-terms [dog Muffet CxThe]
      (is (= #{:shape} (types-of-check kb (list dog Muffet) "CxThe")))
      (is (= #{:shape} (types-of-check kb dog CxThe)))
      ;; a non-map opts is an opts problem, not a shape one — the same
      ;; `:unknown-option` `assert` throws, since `shape-problems` runs its guard
      (is (= #{:unknown-option}
             (into #{} (map :type) (v/check kb (list dog Muffet) CxThe :nope)))))))

(deftest a-bare-sentex-handle-is-refused-because-it-states-nothing
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [CxHandle]
      (let [s (list 'sentexHandle 1)]
        (is (= #{:shape} (types-of-check kb s CxHandle)))
        (doseq [write [v/assert v/assert-inert]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (write kb s CxHandle)))]
            (is (= :shape (:type (ex-data e))))))
        (is (empty? (v/sentexes-matching kb (list 'sentexHandle '?n) CxHandle)))))))

(deftest a-ground-application-in-the-context-slot-is-checked-as-the-context-assert-stores-in
  ;; `assert` reifies the slot to its `cx/` constant whatever is declared about the head
  ;; (docs/context-nat.md), and `check` reads its checks at that constant without minting it
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet SeasonFn Winter]
      (let [slot   (list SeasonFn Winter)
            fact   (list dog Muffet)
            before (v/sentex-count kb)]
        (testing "a slot no constant names yet"
          (is (= [] (v/check kb fact slot)))
          (is (= [] (v/check kb (list 'ist slot fact) 'CxUniverse)))
          (is (= before (v/sentex-count kb)) "and check minted nothing"))
        (testing "a problem in the sentence is the type assert throws"
          (is (= #{:naming} (types-of-check kb (list 'BadPred Muffet) slot)))
          (is (= :naming (assert-type kb (list 'BadPred Muffet) slot))))
        (let [h (v/assert kb fact slot)]
          (testing "a slot assert has minted"
            (is (= [] (v/check kb fact slot))))
          (v/retract! kb h))))))

(deftest a-vector-sentence-is-refused-because-the-read-entry-points-read-it-as-a-join
  ;; The one spelling both entry points accepted and read differently.  A vector is
  ;; `sequential?`, so the write entry point took it and canon flattened it to the list it
  ;; looks like — while a vector goal is what `query` and `prove` spell a *conjunction*
  ;; with, so the same spelling handed back asked for a join over the sentence's own
  ;; elements and answered nothing.  Neither entry point raised.
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob dog CxVec]
      (let [before   (v/sentex-count kb)
            fact     [likesOf Alice Bob]
            rule     ['implies (list dog '?x) (list 'animal '?x)]
            nested   (list 'ist CxVec fact)]
        (testing "assert refuses a vector fact, a vector rule and one inside an ist"
          (doseq [form [fact rule nested]]
            (let [e (is (thrown? clojure.lang.ExceptionInfo (v/assert kb form CxVec))
                        (str (pr-str form) " is refused"))]
              (is (= :shape (:type (ex-data e)))))))
        (testing "check predicts each of them, as it must"
          (doseq [form [fact rule nested]]
            (is (= #{:shape} (types-of-check kb form CxVec)))))
        (testing "and so do the two entry points that share the guard"
          (doseq [entry-point [#(v/assert-inert kb fact CxVec)
                               #(v/check-edit kb {:add [[fact CxVec]]})]]
            (let [r (try (entry-point) (catch clojure.lang.ExceptionInfo e (ex-data e)))]
              (is (= :shape (or (:type r) (:type (first r))))))))
        (testing "the message names the conjunction reading and the spelling to write"
          (let [m (:message (first (v/check kb fact CxVec)))]
            (is (re-find #"conjunction" m))
            (is (re-find #"join over 3" m))
            (is (re-find (re-pattern (str "\\(" likesOf " " Alice " " Bob "\\)")) m))))
        (testing "nothing was stored by any of them"
          (is (= before (v/sentex-count kb))))
        (testing "the list spelling is the one both entry points agree on"
          (let [h (v/assert kb (apply list fact) CxVec)]
            (is (= h (v/handle-of kb (apply list fact) CxVec)))
            (is (seq (v/prove kb (apply list fact) CxVec))
                "the read entry point that answered nothing for the vector answers here")
            (v/retract! kb h)))))))

;; ---- the accepted option keys: admissible knowledge, inadmissible request
;; These two are the request rather than the sentence, and neither is visible after the
;; fact: both store the sentence at a defeat class the caller did not ask for, and a
;; sentex carries no record of the class it was *meant* to have.  So `check` must answer
;; for them, and `assert` must refuse rather than fall back.

(deftest an-opts-key-assert-does-not-read-is-refused-not-defaulted
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob CxThe]
      (let [sentence (list likesOf Alice Bob)]
        (testing "a misspelt key would silently store a default where known-true was meant"
          (is (= #{:unknown-option} (into #{} (map :type)
                                          (v/check kb sentence CxThe {:strenth :monotonic}))))
          (is (= :unknown-option (try (v/assert kb sentence CxThe {:strenth :monotonic}) nil
                                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
        (testing "and the refusal names both the offending key and the key set"
          (let [d (try (v/assert kb sentence CxThe {:strenth :monotonic}) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
            (is (= [:strenth] (:unknown d)))
            (is (= (vec (sort v/assert-opt-keys)) (:options d)))))
        (testing "nothing was stored by either"
          (is (empty? (v/sentexes-matching kb sentence CxThe))))
        (testing "every key in the key set is still accepted"
          (is (empty? (v/check kb sentence CxThe
                               {:strength :monotonic :chain? false :max-depth 8
                                :creator "t" :provenance {:source :test}}))))))))

(deftest a-strength-outside-the-two-classes-is-refused
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob CxThe]
      (let [sentence (list likesOf Alice Bob)]
        (doseq [bad [0.7 :monotonicc nil "monotonic"]]
          (testing (str "strength " (pr-str bad))
            (is (= #{:unknown-option} (into #{} (map :type)
                                            (v/check kb sentence CxThe {:strength bad}))))
            (is (= :unknown-option (try (v/assert kb sentence CxThe {:strength bad}) nil
                                        (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))
        (is (empty? (v/sentexes-matching kb sentence CxThe)))
        (testing "both assertable classes still land"
          (is (some? (v/assert kb sentence CxThe {:strength :monotonic})))
          (is (= :monotonic (v/defeat-class kb (v/handle-of kb sentence CxThe)))))))))

(deftest assert-rule-holds-its-opts-to-the-same-key-set
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [base derived CxThe]
      (let [antes [(list base '?x)] conseq (list derived '?x)]
        (is (= :unknown-option (try (v/assert-rule kb antes conseq CxThe {:dir :forward}) nil
                                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
        (testing ":direction itself is in the key set"
          (is (some? (v/assert-rule kb antes conseq CxThe {:direction :forward}))))))))

;; ---- stratification: the rule-set check runs too ------------------------

(deftest a-rule-closing-a-cycle-through-negation-is-reported-not-stored
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [base aP bP CxThe]
      ;; bP is concluded by a rule whose exception reads aP; a second rule concluding
      ;; aP from bP closes the cycle through that negation
      (v/assert kb (list 'exceptWhen (list aP '?x)
                         (list 'set/defaultRule
                               (list 'implies (list base '?x) (list bP '?x))))
                CxThe)
      (let [cyclic (list 'implies (list bP '?x) (list aP '?x))
            ps     (v/check kb cyclic CxThe)]
        (is (= #{:not-stratified} (into #{} (map :type) ps)))
        (testing "and the reported cycle is the one the refusal names"
          (is (seq (:cycle (first ps)))))
        (is (= :not-stratified (assert-type kb cyclic CxThe)))))))

;; A `different` antecedent is negation as failure over the equality closure
;; (`checks/negative-predicates`), so a rule reading it carries a negative edge while
;; carrying no exception — and nothing registers such a rule for re-checking, so the
;; watched-rule set does not name it.  Both stratification entry points have to find it
;; anyway (`checks/negative-edge-rules`), or the same pair of rules is refused in one
;; arrival order and stored in the other.

(defn- different-cycle-rules
  "The unstratified pair: the negative half reads `different` and concludes `qP`, the
  positive half forward-chains an equality from `qP`, so its conclusions are stored and
  merge.  `equality` is what closes the ring — `sameAs` directly, or a predicate a `genl`
  edge later puts underneath it.  With `:backward` the positive half is backward-only."
  ([aP qP equality] (different-cycle-rules aP qP equality :forward))
  ([aP qP equality direction]
   [(list 'implies (list 'and (list aP '?x '?y) (list 'different '?x '?y))
          (list qP '?x '?y))
    (list (if (= :backward direction) 'set/backwardRule 'set/forwardRule)
          (list 'implies (list qP '?x '?y) (list equality '?x '?y)))]))

(deftest a-different-antecedent-closes-a-cycle-in-either-arrival-order
  (testing "the positive half arrives last — the negative edge is a stored rule's"
    (tu/with-neutral-kb [kb kb-with-starter]
      (tu/with-terms [aP qP CxThe]
        (let [[neg pos] (different-cycle-rules aP qP 'sameAs)]
          (v/assert kb neg CxThe)
          (is (= #{:not-stratified} (types-of-check kb pos CxThe)))
          (is (= :not-stratified (assert-type kb pos CxThe)))
          (is (empty? (v/sentexes-matching kb pos '?ctx)))))))
  (testing "the negative half arrives last — the same rule set, the same refusal"
    (tu/with-neutral-kb [kb kb-with-starter]
      (tu/with-terms [aP qP CxThe]
        (let [[neg pos] (different-cycle-rules aP qP 'sameAs)]
          (v/assert kb pos CxThe)
          (is (= :not-stratified (assert-type kb neg CxThe))))))))

(deftest a-genl-edge-closing-a-cycle-round-a-different-antecedent-is-refused
  ;; the edge path: both rules are stratified until the edge puts `zSame` under `sameAs`,
  ;; which is when the negative edge out of the `different` rule reaches the rule
  ;; concluding `zSame`.
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [aP qP zSame unrelated CxThe]
      (let [[neg pos] (different-cycle-rules aP qP zSame)
            edge      (list 'genl zSame 'sameAs)]
        (v/assert kb neg CxThe)
        (v/assert kb pos CxThe)
        (is (= #{:not-stratified} (types-of-check kb edge CxThe)))
        (is (= :not-stratified (assert-type kb edge CxThe)))
        (testing "and it leaves nothing behind"
          (is (empty? (v/sentexes-matching kb edge '?ctx))))
        (testing "an edge that closes no cycle still lands, so the refusal is the cycle"
          (is (some? (v/assert kb (list 'genl zSame unrelated) CxThe))))))))

(deftest a-backward-only-equality-rule-closes-no-cycle-round-a-different-antecedent
  ;; `different` reads the stored merges, and a backward-only rule stores no conclusion,
  ;; so the pair is stratified in either arrival order and under the `genl` edge too
  (doseq [order [:neg-first :pos-first :edge-last]]
    (tu/with-neutral-kb [kb kb-with-starter]
      (tu/with-terms [aP qP zSame CxThe]
        (let [[neg pos] (different-cycle-rules aP qP zSame :backward)
              edge      (list 'genl zSame 'sameAs)
              sentences (case order
                          :neg-first [edge neg pos]
                          :pos-first [edge pos neg]
                          :edge-last [neg pos edge])]
          (is (= [nil nil nil] (mapv #(assert-type kb % CxThe) sentences))
              (str order)))))))

(deftest a-rule-reading-different-beside-the-starters-time-slice-equality-is-stored
  ;; the starter's `(equals (CxTimeFn (CxTimeFn ?c ?t1) ?t2) …)` rule reads `time` and is
  ;; backward-only; a forward rule reading `different` and concluding a kind of
  ;; `uninterrupted` reaches it through the `time`/`uninterrupted` intersection rule, and
  ;; reaches core.txt's inert mint rule concluding `genl` through `subtimeOf`
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [odd_receipt receipt sameKey CxThe]
      (v/assert kb (list 'genl odd_receipt 'uninterrupted) CxThe)
      (is (nil? (assert-type kb (list 'set/forwardRule
                                      (list 'implies
                                            (list 'and (list receipt '?a) (list receipt '?b)
                                                  (list sameKey '?a '?b) (list 'different '?a '?b))
                                            (list odd_receipt '?a)))
                             CxThe))))))

(deftest an-exceptWhen-naming-a-handle-is-checked-as-assert-checks-it
  ;; `(exceptWhen Q (sentexHandle H))` amends a stored rule, so `check` answers from the
  ;; stored record rather than from a rule form; each row is refused by `assert` with the
  ;; type `check` reports
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog barks quiet base b_p a_p Rex CxThe]
      (let [fact  (v/assert kb (list dog Rex) CxThe)
            rule  (v/assert kb (list 'implies (list dog '?x) (list barks '?x)) CxThe)
            r1    (v/assert kb (list 'implies (list base '?x) (list b_p '?x)) CxThe)
            _     (v/assert kb (list 'implies (list b_p '?x) (list a_p '?x)) CxThe)
            by    (fn [q h] (list 'exceptWhen q (list 'sentexHandle h)))
            before (v/sentex-count kb)]
        (doseq [[label sentence expected]
                [["a handle naming a fact"         (by (list quiet '?x) fact)   :not-well-formed]
                 ["a handle naming nothing stored" (by (list quiet '?x) 999999) :not-well-formed]
                 ["a variable the rule never binds" (by (list quiet '?y) rule)  :exception-not-closed]
                 ["a query literal misnamed"       (by (list 'Quiet '?x) rule)  :naming]
                 ;; `a_p` follows from `b_p`, which the excepted rule concludes, so the
                 ;; exception is a negative edge closing a cycle
                 ["a cycle through the new negative edge" (by (list a_p '?x) r1) :not-stratified]]]
          (testing label
            (is (= #{expected} (types-of-check kb sentence CxThe)))
            (is (= expected (assert-type kb sentence CxThe)))))
        (is (= before (v/sentex-count kb)) "no refusal stored anything")
        (testing "an exception the rule closes is admissible, and lands"
          (is (= [] (v/check kb (by (list quiet '?x) rule) CxThe)))
          (is (nat-int? (v/assert kb (by (list quiet '?x) rule) CxThe))))))))

(deftest an-edit-batch-that-is-not-a-map-or-names-an-unknown-key-is-refused
  ;; `check-edit` reports and `edit!` throws the one problem, so the dry run predicts it
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Rex CxThe]
      (doseq [[label batch mismatch unknown]
              [["a vector of entries"   [[(list dog Rex) CxThe]]           :not-a-map   nil]
               ["one misspelt key"      {:adds [[(list dog Rex) CxThe]]}   :unknown-key [:adds]]
               ["two misspelt keys"     {:adds [] :removes []}             :unknown-key [:adds :removes]]]]
        (testing label
          (let [[p & more] (v/check-edit kb batch)
                thrown     (try (v/edit! kb batch) nil
                                (catch clojure.lang.ExceptionInfo e (ex-data e)))]
            (is (nil? more))
            (is (= [:unknown-option mismatch unknown] ((juxt :type :mismatch :unknown) p)))
            (is (= [:unknown-option mismatch] ((juxt :type :mismatch) thrown)))
            (when unknown
              (is (re-find (re-pattern (str "unknown edit batch key" (when (next unknown) "s")
                                            " :adds"))
                           (:message p)))))))
      (is (nil? (v/handle-of kb (list dog Rex) CxThe)) "and nothing was written"))))

(deftest a-malformed-connective-frame-is-refused-at-both-entry-points
  ;; `sx/connective-problems` and the literal checks behind it: one row per refusal,
  ;; each asked of `check`, `assert` and `try-assert` alike
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog pet barks quiet owns Rex CxThe]
      (let [rule   (list 'implies (list dog '?x) (list barks '?x))
            before (v/sentex-count kb)]
        (doseq [[label sentence expected]
                [["an empty form"                        ()                                  :not-well-formed]
                 ["a rule wrapper with no rule"          (list 'set/defaultRule)             :not-well-formed]
                 ["a rule wrapper with two rules"        (list 'set/forwardRule rule rule)   :not-well-formed]
                 ["a constraint wrapper with no rule"    (list 'set/hardConstraint)          :not-well-formed]
                 ["a constraint wrapper with two levels" (list 'set/softConstraint 2 3 rule) :not-well-formed]
                 ["an exceptWhen with no rule"           (list 'exceptWhen (list quiet '?x)) :not-well-formed]
                 ["an exceptWhen with a third argument"  (list 'exceptWhen (list quiet '?x) rule Rex)
                  :not-well-formed]
                 ["a rule as an antecedent literal"
                  (list 'implies (list 'and (list dog '?x) (list 'implies (list pet '?x) (list dog '?x)))
                        (list barks '?x))                                                  :not-well-formed]
                 ["a rule as an exception literal"
                  (list 'exceptWhen (list 'implies (list pet '?x) (list quiet '?x)) rule)  :not-well-formed]
                 ["a head existential in an antecedent"
                  (list 'implies (list 'and (list dog '?x) (list 'exists '?y (list owns '?x '?y)))
                        (list barks '?x))                                                  :not-well-formed]
                 ["the anonymous variable in an exception"
                  (list 'exceptWhen (list owns '?x '_) rule)                               :exception-not-closed]
                 ["a definition at the wrong arity"      (list 'defnSufficient dog Rex Rex)  :not-well-formed]
                 ;; no prover answers a negated query (docs/naf.md)
                 ["a negated universal in an exception"
                  (list 'exceptWhen (list 'not (list 'forall '?y (list 'implies (list owns '?x '?y)
                                                                       (list pet '?y))))
                        rule)                                                              :not-well-formed]
                 ["a negated existential in an antecedent"
                  (list 'implies (list 'and (list dog '?x)
                                       (list 'not (list 'thereExists '?y (list owns '?x '?y))))
                        (list barks '?x))                                                  :not-well-formed]
                 ["a negated unknown in an antecedent"
                  (list 'implies (list 'and (list dog '?x) (list 'not (list 'unknown (list pet '?x))))
                        (list barks '?x))                                                  :not-well-formed]
                 ["a negated universal under an unknown antecedent"
                  (list 'implies (list 'and (list dog '?x)
                                       (list 'unknown
                                             (list 'and (list pet '?x)
                                                   (list 'not (list 'forall '?y
                                                                    (list 'implies (list owns '?x '?y)
                                                                          (list dog '?y)))))))
                        (list barks '?x))                                                  :not-well-formed]]]
          (testing label
            (is (= #{expected} (types-of-check kb sentence CxThe)))
            (is (= expected (assert-type kb sentence CxThe)))
            (is (= expected (try (v/try-assert kb sentence CxThe) nil
                                 (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))
        (is (= before (v/sentex-count kb)) "no refusal stored anything")))))

;; ---- encodability: what a sentence's content may be ----------------------
;; A map or a set has no canonical form, so `sentex/canon` cannot normalize one and
;; `nm/form-rank` cannot order one — the entry point refuses it rather than storing a sentence
;; whose durable bytes and whose content order both depend on how it was built.

(deftest a-map-or-set-anywhere-in-a-sentence-is-refused
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [holds Tom CxThe]
      (doseq [[label arg] [["a map argument"            {:a 1}]
                           ["a set argument"            #{1 2}]
                           ["a map inside a vector"     [1 {:a 1}]]
                           ["a set inside a compound"   (list 'ListFn #{1 2})]]]
        (testing label
          (let [sentence (list holds Tom arg)]
            (is (= #{:not-encodable} (types-of-check kb sentence CxThe)))
            (is (= :not-encodable (assert-type kb sentence CxThe)))
            (is (empty? (v/sentexes-matching kb sentence CxThe))))))
      (testing "a rule literal is walked too — the whole rule is one sentence"
        (is (= :not-encodable
               (assert-type kb (list 'implies (list holds '?x {:a 1}) (list holds '?x Tom))
                            CxThe))))
      (testing "the sequential the refusal points at is accepted"
        (is (some? (v/assert kb (list holds Tom [[:a 1] [:b 2]]) CxThe)))))))

;; ---- the batch form -----------------------------------------------------

(deftest check-edit-points-at-the-entry-that-is-wrong
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice Bob CxThe]
      (let [h  (v/assert kb (list likesOf Alice Bob) CxThe)
            ps (v/check-edit kb {:add    [[(list likesOf Alice Bob) CxThe]
                                          [(list likesOf Alice '?x) CxThe]
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
  ;; the constraint-only reading: the second add is a genlArg refusal there
  (tu/without-entailing
   ;; Nothing is stored, so each add is judged against the KB *before the batch*, not
   ;; against the KB the entries before it would have made.  That is the correct answer
   ;; for a dry run, and it differs from the sequential reading in **both** directions —
   ;; so both are asserted, because an assertion true under either reading says nothing
   ;; about which one `check-edit` implements.
   (tu/with-neutral-kb [kb kb-with-starter]
     (testing "an add admissible only *after* an earlier one landed is still reported"
       ;; sequentially the quotedArg declaration lands first and makes the application at
       ;; position 1 a mention, which no input declaration of its function reaches; as it
       ;; stands the position is not quoted, and the string input is convicted
       (tu/with-terms [relOf InputFn an_animal Rex CxThe]
         (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
         (v/assert kb (list 'genl an_animal 'thing) 'CxUniverse)
         (v/assert kb (list 'unreifiable_function InputFn) 'CxUniverse)
         (v/assert kb (list 'unary_function InputFn) 'CxUniverse)
         (v/assert kb (list 'arg InputFn 1 an_animal) 'CxUniverse)
         (let [ps (v/check-edit kb {:add [[(list 'quotedArg relOf 1 'thing) CxThe]
                                          [(list relOf (list InputFn "x") Rex) CxThe]]})]
           (is (= [{:in :add :index 1 :type :arg-type}]
                  (mapv #(select-keys % [:in :index :type]) ps))
               "the second add was judged against a KB the first had already changed"))))
     (testing "and an add the KB as it stands admits is *not* reported for what an
              earlier one would have forbidden"
       ;; the mirror: sequentially the declaration binds the fact after it and the arity
       ;; check refuses; as it stands nothing is declared and open world admits it
       (tu/with-terms [pOf Thing CxThe]
         (let [ps (v/check-edit kb {:add [[(list 'binary_predicate pOf) CxThe]
                                          [(list pOf Thing) CxThe]]})]
           (is (= [] ps)
               "the declaration in the same batch was give the impression that it had landed"))))
     (testing "and the open-world floor still holds: an untyped argument violates nothing"
       (tu/with-terms [newPred Thing CxThe]
         (is (= [] (v/check-edit kb {:add [[(list 'arg newPred 1 'animal) CxThe]
                                           [(list newPred Thing) CxThe]]}))))))))

;; ---- which declaration a violation names: content, not arrival ----------

(deftest ^:slow an-arg-type-violation-names-the-content-sorted-declaration
  ;; two visible arg declarations convict the same sentence, one per argument;
  ;; the single reported violation must name the content-sort winner in every
  ;; assertion order — `res/matches-visible` promises the answer *set*, so
  ;; enumeration order may not pick the declaration a conviction is about.  Forced to the
  ;; constraint-only reading: under the entailing one a declaration derives its type of a
  ;; symbol argument and convicts nothing, so there is no violation to name
  (doseq [flip? [false true]]
    (tu/without-entailing
     (tu/with-neutral-kb [kb kb-with-starter]
       (tu/with-terms [relOf t_first t_second t_plain Muffet Alice CxThe]
         (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
         (doseq [t [t_first t_second t_plain]]
           (v/assert kb (list 'genl t 'thing) 'CxUniverse))
         (doseq [t [t_first t_second]]
           (v/assert kb (list 'disjoint t_plain t) 'CxUniverse))
         (let [d1     (list 'arg relOf 1 t_first)
               d2     (list 'arg relOf 2 t_second)
               winner (first (sort-by pr-str [d1 d2]))]
           (doseq [d (if flip? [d2 d1] [d1 d2])]
             (v/assert kb d 'CxUniverse))
           (v/assert kb (list t_plain Muffet) CxThe)
           (v/assert kb (list t_plain Alice) CxThe)
           (let [p (tu/write-conviction kb (list relOf Muffet Alice) CxThe)]
             (testing (str "assertion order " (if flip? "second first" "first second"))
               (is (= :arg-type (:type p)) "both declarations convict, so a violation is reported")
               (is (= (nth winner 2) (:position p)))
               (is (= (nth winner 3) (:expected p)))))))))))

;; ---- an imperative is an instruction, so there is no verdict to predict ---

(deftest a-do-imperative-is-reported-not-checkable-rather-than-refused
  ;; `check` promises what `assert` would do, and what `assert` does with a `do/` form is
  ;; *run* it — nothing is stored, so there is no admissibility to answer.  The answer is
  ;; a problem row rather than a throw because the caller is an editor grading lines: an
  ;; imperative is a line it may not grade, not a request it got wrong.  The `:type` is
  ;; how it tells the two apart, since every other row on this route is a refusal.
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [CxPlan]
      (let [before (v/sentex-count kb)]
        (doseq [imperative [(list 'do/label CxPlan CxPlan :one)
                            (list 'do/labeling CxPlan)]]
          (testing (str (first imperative) " is reported rather than graded")
            (let [problems (v/check kb imperative 'CxUniverse)]
              (is (= [:not-checkable] (mapv :type problems)))
              (is (= imperative (:sentence (first problems)))
                  "and the row names the form, so an editor can say which line"))))
        (testing "and reporting ran none of them — check reads, it does not act"
          (is (= before (v/sentex-count kb))))))))

;; ---- ist and the wrappers dispatch the way assert does ------------------

(deftest check-follows-assert-into-ist-and-the-rule-wrappers
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [likesOf Alice CxIst]
      (testing "(ist Ctx S) is checked as S in Ctx"
        (is (= #{:not-ground}
               (types-of-check kb (list 'ist CxIst (list likesOf Alice '?x)) 'CxUniverse))))
      (testing "a set/*Rule wrapper is checked as the rule it wraps"
        (is (= #{:not-range-restricted}
               (types-of-check kb (list 'set/forwardRule
                                        (list 'implies (list 'dog '?x) (list 'animal '?y)))
                               CxIst)))))))

(deftest an-ist-form-holds-exactly-three-elements
  ;; `(ist Ctx S)` is the form, and both `assert` and `check` read it by position — so a
  ;; wrong length has to be refused rather than indexed into.  Two elements reached
  ;; `(nth sentence 2)`; four asserted with the extra silently dropped, which is the
  ;; worse of the two because it stores something the caller did not write.
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [dog Muffet CxIst]
      (let [short-form (list 'ist CxIst)
            long-form  (list 'ist CxIst (list dog Muffet) 'junk)]
        (testing "check reports the shape rather than raising out of nth"
          (is (= #{:shape} (types-of-check kb short-form 'CxUniverse)))
          (is (= #{:shape} (types-of-check kb long-form 'CxUniverse))))
        (testing "and assert refuses both with the same :type"
          (doseq [form [short-form long-form]]
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (v/assert kb form 'CxUniverse))
                        (str (pr-str form) " is refused"))]
              (is (= :shape (:type (ex-data e)))))))
        (testing "and the over-long one stored nothing"
          (is (empty? (v/sentexes-matching kb (list dog '?x) CxIst))))))))

(deftest ist-reads-nothing-so-it-is-refused-anywhere-it-would-have-to
  ;; `ist` names a context at the `assert` and read entry points.  Put one where a rule
  ;; *reads* and it is indexed and matched under
  ;; the functor `ist`, which no sentex carries — so it satisfies nothing, and the rule
  ;; decides itself on a context it never consulted.  Four layers already read the frame
  ;; as meaningful (the naming check descends the context slot, range restriction counts
  ;; its variables as bound, canonicalization sorts it by the inner predicate), which is
  ;; what makes silence here a rule the engine reported as accepted.
  ;;
  ;; The exception and NAF frames are why it is refused rather than left inert: an
  ;; unmatchable `exceptWhen` query is a guard that never guards, and an unmatchable
  ;; `unknown` is satisfied by that same emptiness, so the rule fires unconditionally.
  ;; A rule that does nothing announces itself; a guard that passes everything does not.
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [dog barks Muffet CxIst]
      (let [before (v/sentex-count kb)
            ante   (list 'ist CxIst (list dog '?x))
            reads  {"a positive antecedent"
                    (list 'implies ante (list barks '?x))
                    "one antecedent of a conjunction"
                    (list 'implies (list 'and (list dog '?x) ante) (list barks '?x))
                    "a negated antecedent"
                    (list 'implies (list 'and (list dog '?x) (list 'not ante))
                          (list barks '?x))
                    "a NAF antecedent"
                    (list 'implies (list 'and (list dog '?x) (list 'unknown ante))
                          (list barks '?x))
                    "an exceptWhen query"
                    (list 'exceptWhen ante (list 'implies (list dog '?x) (list barks '?x)))}]
        (doseq [[label sentence] reads]
          (testing label
            (is (= #{:not-well-formed} (types-of-check kb sentence 'CxUniverse)))
            (is (= :not-well-formed (assert-type kb sentence 'CxUniverse))
                "and it is the type assert throws for the same sentence")))
        (testing "the message names the two ways to make S visible instead"
          (let [msg (:message (first (v/check kb (list 'implies ante (list barks '?x))
                                              'CxUniverse)))]
            (is (re-find #"decontextualized_predicate" msg))
            (is (re-find #"genlCx" msg))))
        (testing "an ist consequent is refused too: it would place the conclusion in a
                  context that need not see the rule or the facts"
          (let [placing (list 'implies (list dog '?x) (list 'ist CxIst (list barks '?x)))]
            (is (= #{:not-well-formed} (types-of-check kb placing 'CxUniverse)))
            (is (= :not-well-formed (assert-type kb placing 'CxUniverse)))
            (is (re-find #"decontextualized_predicate"
                         (:message (first (v/check kb placing 'CxUniverse)))))))
        (testing "and nothing any of it named was stored"
          (is (= before (v/sentex-count kb))))))))

(deftest the-NAF-literal-checks-are-predicted-not-only-thrown
  ;; These live in `sentex/check-naf-closed`, which the constructor runs — so both
  ;; *storage* entry points had them and the dry-run entry point did not, `check` predicting an assert
  ;; without building a sentex.  A caller validating a rule before writing it was told
  ;; the rule was admissible and then handed a throw, which is the one answer `check`
  ;; must never give.  Now in `checks/check-rule!`, the list every entry point reads.
  (tu/with-neutral-kb [kb kb-with-starter]
    (tu/with-terms [person likes kidOf sick adult loner]
      (let [before (v/sentex-count kb)]
        (doseq [[label sentence expected]
                [["an unknown whose variable no generator binds"
                  (list 'implies (list 'and (list person '?x) (list 'unknown (list likes '?x '?z)))
                        (list loner '?x))
                  :naf-not-closed]
                 ["a conjunct of one that is open — closure is per conjunct"
                  (list 'implies (list 'and (list person '?x)
                                       (list 'unknown (list 'and (list adult '?x)
                                                            (list likes '?x '?z))))
                        (list loner '?x))
                  :naf-not-closed]
                 ["a quantified variable escaping its thereExists"
                  (list 'implies (list 'and (list person '?x) (list 'thereExists '?x (list adult '?x)))
                        (list loner '?x))
                  :quantifier-not-local]
                 ["a quantified variable no generator conjunct of the query produces"
                  (list 'implies (list 'and (list person '?x)
                                       (list 'unknown (list 'thereExists '?c
                                                            (list 'and (list kidOf '?x '?x)
                                                                  (list 'unknown (list sick '?c))))))
                        (list loner '?x))
                  :naf-not-closed]
                 ["an aggregate whose reduction variable no census conjunct produces"
                  (list 'implies (list 'and (list person '?x)
                                       (list 'agg/count '?n '?c
                                             (list 'and (list kidOf '?x '?x)
                                                   (list 'unknown (list sick '?c))))
                                       (list 'lessThan 1 '?n))
                        (list loner '?x))
                  :naf-not-closed]
                 ["an aggregate reducing over a constant"
                  (list 'implies (list 'and (list person '?x)
                                       (list 'agg/count '?n 'Ada (list kidOf '?x 'Ada)))
                        (list loner '?x))
                  :not-well-formed]
                 ["a thereExists whose binder is a constant"
                  (list 'implies (list 'and (list person '?x)
                                       (list 'unknown (list 'thereExists 'Kid (list kidOf '?x 'Kid))))
                        (list loner '?x))
                  :not-well-formed]
                 ["a thereExists whose binder list holds a constant"
                  (list 'implies (list 'and (list person '?x)
                                       (list 'unknown (list 'thereExists (list '?c 'Kid)
                                                            (list 'and (list kidOf '?x '?c)
                                                                  (list likes '?c 'Kid)))))
                        (list loner '?x))
                  :not-well-formed]
                 ["a forall whose binder is a constant"
                  (list 'implies (list 'and (list person '?x)
                                       (list 'forall 'Kid (list 'implies (list kidOf '?x 'Kid)
                                                                (list sick 'Kid))))
                        (list loner '?x))
                  :not-well-formed]
                 ["a forall whose binder list holds a constant"
                  (list 'implies (list 'and (list person '?x)
                                       (list 'forall (list '?c 'Kid)
                                             (list 'implies (list kidOf '?x '?c)
                                                   (list likes '?c 'Kid))))
                        (list loner '?x))
                  :not-well-formed]
                 ["a head exists whose binder is a constant"
                  (list 'implies (list person '?x) (list 'exists 'Kid (list kidOf '?x 'Kid)))
                  :not-well-formed]
                 ["a matchesPattern whose pattern no antecedent binds"
                  (list 'implies (list 'and (list likes '?x '?s) (list 'matchesPattern '?s '?p))
                        (list loner '?x))
                  :naf-not-closed]
                 ["an empty NAF conjunction, which nothing can make derivable"
                  (list 'implies (list 'and (list person '?x) (list 'unknown (list 'and)))
                        (list loner '?x))
                  :not-well-formed]]]
          (testing label
            (is (= #{expected} (types-of-check kb sentence 'CxUniverse)))
            (is (= [expected] (map :type (v/check-edit kb {:add [[sentence 'CxUniverse]]}))))
            (is (= expected (assert-type kb sentence 'CxUniverse))
                "and it is the type assert throws for the same sentence")))
        (testing "and the well-formed conjunctive rule is admissible at both entry points"
          (is (= [] (v/check kb (list 'implies (list 'and (list person '?x)
                                                     (list 'unknown (list 'and (list adult '?x)
                                                                          (list sick '?x))))
                                      (list loner '?x))
                             'CxUniverse))))
        (testing "and so is the quantified conjunction the join now answers"
          (is (= [] (v/check kb (list 'implies (list 'and (list person '?x)
                                                     (list 'unknown
                                                           (list 'thereExists '?c
                                                                 (list 'and (list kidOf '?x '?c)
                                                                       (list sick '?c)))))
                                      (list loner '?x))
                             'CxUniverse))))
        (testing "and so is the conjunctive census body, which is joined the same way"
          (is (= [] (v/check kb (list 'implies (list 'and (list person '?x)
                                                     (list 'agg/count '?n '?c
                                                           (list 'and (list kidOf '?x '?c)
                                                                 (list sick '?c)))
                                                     (list 'lessThan 1 '?n))
                                      (list loner '?x))
                             'CxUniverse))))
        (testing "and nothing any of it named was stored"
          (is (= before (v/sentex-count kb))))))))

;; ---- assert-inert runs the same shape guards ----------------------------

(deftest assert-inert-refuses-the-shapes-assert-refuses
  ;; `assert-inert` skips the constraint / wff / chaining machinery on purpose — a
  ;; materialized head is already well-formed — but the shape guards are not machinery,
  ;; they are what keeps a non-sentence out of the store.  `nm/literals` of a
  ;; non-sequential sentence finds no literals, so a string or nil would pass the naming
  ;; check vacuously and store as an object no query can match.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxInert]
      (let [before (v/sentex-count kb)]
        (testing "a non-sequential sentence is :shape, as at assert"
          (doseq [bad ["(dog Muffet)" nil 42 {:a 1}]]
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (v/assert-inert kb bad CxInert))
                        (str (pr-str bad) " is refused"))]
              (is (= :shape (:type (ex-data e)))))))
        (testing "a non-symbol context is :shape, not :naming"
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (v/assert-inert kb (list dog Muffet) (str CxInert))))]
            (is (= :shape (:type (ex-data e))))))
        (testing "and nothing was stored by any refusal"
          (is (= before (v/sentex-count kb)))))
      (testing "a well-formed inert sentex still stores, unbelieved"
        (let [h (v/assert-inert kb (list dog Muffet) CxInert)]
          (is (nat-int? h))
          (is (not (v/in? kb h)) "inert means never a premise")
          (v/retract! kb h))))))

(deftest assert-inert-refuses-an-open-sentence-and-resolves-an-ist-form
  ;; Two more of `assert`'s own readings, at the entry point that persists and indexes
  ;; without premising.  An open literal stored inert is a record a `CxEverything` read
  ;; answers as a fact, and a stored sentence is closed (`checks/check-ground`).  An
  ;; `(ist Ctx S)` stored as written is a record with the `ist` functor, which
  ;; `handle-of`, `contexts-of` and every read resolve past — stored, and reachable by
  ;; nothing.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxInert]
      (let [before (v/sentex-count kb)]
        (testing "an open sentence is :not-ground, as at assert"
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (v/assert-inert kb (list dog '?x) CxInert)))]
            (is (= :not-ground (:type (ex-data e))))))
        (testing "a malformed ist is :shape, as at assert"
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (v/assert-inert kb (list 'ist CxInert) 'CxUniverse)))]
            (is (= :shape (:type (ex-data e))))))
        (testing "and nothing was stored by either refusal"
          (is (= before (v/sentex-count kb)))))
      (testing "an (ist Ctx S) stores S in Ctx, unbelieved, where handle-of finds it"
        (let [h (v/assert-inert kb (list 'ist CxInert (list dog Muffet)) 'CxUniverse)]
          (is (= (list dog Muffet) (:sentence (v/sentex kb h))))
          (is (= CxInert (:context (v/sentex kb h))))
          (is (= h (v/handle-of kb (list dog Muffet) CxInert)))
          (is (not (v/in? kb h)) "inert means never a premise")
          (v/retract! kb h))))))

(deftest assert-inert-refuses-what-assert-refuses-on-the-sentence-alone
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxInert]
      (let [h      (v/assert kb (list dog Muffet) CxInert)
            before (v/sentex-count kb)]
        (doseq [[type sentence] [[:derived-only (list 'defeat (list 'sentexHandle h))]
                                 [:not-well-formed (list 'genl dog dog)]
                                 [:unknown-handle (list 'except (list 'sentexHandle 99999999))]
                                 [:not-assertible (list 'do/nosuch CxInert)]]]
          (testing (pr-str sentence)
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (v/assert-inert kb sentence CxInert)))]
              (is (= type (:type (ex-data e)))))))
        (is (= before (v/sentex-count kb)) "no refusal stored a record")))))

(deftest assert-inert-refuses-a-rule
  ;; A rule is indexed where it is *created* — `assert-rule-sentence`'s new branch and
  ;; the generator mint — so one stored by this entry point is one no chainer can reach, and it
  ;; stays unreachable: asserting the same rule afterwards resolves to the stored sentex,
  ;; takes the existing branch and does not index it either.  What that leaves is a rule
  ;; `in?` calls believed and no fact ever fires, which is the accepted-and-inert state
  ;; `check-generator` refuses at the other entry point.  A labeling labels atoms.
  ;;
  ;; The *other* inertness is the rule's own `set/inertRule` — believed, indexed and
  ;; browsable, firing neither way — which is what a documentation-only rule wants (a
  ;; transitivity the cached closure computes instead) and what
  ;; `direction_test/inert-rule-is-documentation-only` asserts.  The refusal's message names
  ;; it, since a caller reaching for this entry point usually meant that one.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bird flies Tweety CxInert]
      (let [before (v/sentex-count kb)
            rule   (list 'implies (list bird '?x) (list flies '?x))]
        (doseq [[what sentence] [["a bare implies"      rule]
                                 ["a set/defaultRule"   (list 'set/defaultRule rule)]
                                 ["a set/backwardRule"  (list 'set/backwardRule rule)]]]
          (testing what
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (v/assert-inert kb sentence CxInert)))]
              (is (= :not-indexable (:type (ex-data e)))
                  "the type check-generator uses for a rule that cannot exercise what it claims"))))
        (is (= before (v/sentex-count kb)) "and no refusal stored anything")
        (testing "the atoms a labeling actually materializes are untouched"
          (let [h  (v/assert-inert kb (list bird Tweety) CxInert)
                nh (v/assert-inert kb (list 'not (list bird Tweety)) CxInert)]
            (is (nat-int? h))
            (is (nat-int? nh))
            (is (not (v/in? kb h)))
            (v/retract! kb h)
            (v/retract! kb nh)))))))
