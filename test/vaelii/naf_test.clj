;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.naf-test
  "Negation as failure: `(unknown S)` and `(thereExists ?x S)`.

  `unknown` is closed-world negation — it holds exactly while `S` is not derivable —
  and `thereExists` existentially closes a variable off, so `(unknown (thereExists ?x
  S))` says 'there is no x such that S'.  Both are answered by a prover at level 6 (no
  backchaining), are ground/closed only, and store nothing.  See docs/naf.md."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

;; ---- free-vars: what "fully bound to evaluate" means --------------------

(deftest free-vars-respects-the-quantifier
  (testing "a plain literal contributes every variable"
    (is (= '#{?x ?y} (sx/free-vars '(parentOf ?x ?y)))))
  (testing "unknown is transparent"
    (is (= '#{?x} (sx/free-vars '(unknown (flies ?x))))))
  (testing "thereExists subtracts its binder, so a closed existential has no free var"
    (is (= #{} (sx/free-vars '(thereExists ?x (parentOf ?x Tom)))))
    (is (= '#{?y} (sx/free-vars '(thereExists ?x (parentOf ?x ?y))))))
  (testing "the two combine — (unknown (thereExists ?x (P ?x ?y))) is free only in ?y"
    (is (= '#{?y} (sx/free-vars '(unknown (thereExists ?x (parentOf ?x ?y))))))
    (is (= #{}    (sx/free-vars '(unknown (thereExists ?x (parentOf ?x Tom)))))))
  (testing "a conjunction contributes every conjunct's variables, so closure covers all of them"
    (is (= '#{?x ?y} (sx/free-vars '(unknown (and (flies ?x) (parentOf ?x ?y))))))
    (is (= '#{?x} (sx/free-vars '(unknown (and (thereExists ?c (parentOf ?x ?c))
                                               (adult ?x))))))))

(deftest naf-query-conjuncts-flattens-to-what-is-evaluated
  (testing "a bare literal is one conjunct"
    (is (= '[(flies Tweety)] (sx/naf-query-conjuncts '(unknown (flies Tweety))))))
  (testing "a conjunction is its conjuncts"
    (is (= '[(flies Tweety) (adult Tweety)]
           (sx/naf-query-conjuncts '(unknown (and (flies Tweety) (adult Tweety)))))))
  (testing "nesting is flattened — a nested `and` is a goal no prover claims"
    (is (= '[(a X) (b X) (c X)]
           (sx/naf-query-conjuncts '(unknown (and (a X) (and (b X) (c X))))))))
  (testing "a quantifier is left intact: it is the prover's, not the flattener's"
    (is (= '[(thereExists ?c (parentOf ?c Tom))]
           (sx/naf-query-conjuncts '(unknown (thereExists ?c (parentOf ?c Tom))))))))

;; ---- unknown: closed-world negation -------------------------------------

(tu/deftest-kb unknown-holds-for-what-is-not-derivable
  (tu/with-terms [flies happy Tweety]
    (v/assert kb (list 'flies Tweety) 'CxWell)
    (testing "a fact that is not stored is unknown"
      (is (v/ask? kb (list 'unknown (list 'happy Tweety))))
      (is (not (v/ask? kb (list 'unknown (list 'flies Tweety))))
          "a stored, believed fact is NOT unknown"))))

(tu/deftest-kb unknown-follows-belief-a-later-fact-flips-it
  (tu/with-terms [flies Tweety]
    (testing "before the fact arrives, the literal is unknown"
      (is (v/ask? kb (list 'unknown (list 'flies Tweety)))))
    (let [h (v/assert kb (list 'flies Tweety) 'CxWell)]
      (testing "once asserted and believed, it is no longer unknown"
        (is (not (v/ask? kb (list 'unknown (list 'flies Tweety))))))
      (v/retract! kb h)
      (testing "retracting the fact makes it unknown again"
        (is (v/ask? kb (list 'unknown (list 'flies Tweety))))))))

(tu/deftest-kb unknown-refuses-an-open-goal
  ;; "must be fully bound to evaluate": an open `(unknown (flies ?x))` is not a test
  ;; but a search over the whole domain's complement, so the NAF prover refuses it —
  ;; exactly the refusal `different` makes (FactProver is always listed, but it
  ;; finds no stored `(unknown ...)` fact, so nothing answers).
  (let [applicable (fn [goal] (set (map :prover (v/query-plan kb goal '?ctx))))]
    (testing "the NAF prover claims a *closed* unknown"
      (is (contains? (applicable '(unknown (flies Tweety))) "UnknownProver")))
    (testing "but refuses an *open* one"
      (is (not (contains? (applicable '(unknown (flies ?x))) "UnknownProver")))
      (is (not (v/ask? kb '(unknown (flies ?x))))))))

;; ---- thereExists: existential closure -----------------------------------

(tu/deftest-kb there-exists-is-a-witnessed-existence-check
  (tu/with-terms [parentOf Ann Tom Nemo]
    (v/assert kb (list 'parentOf Ann Tom) 'CxWell)
    (testing "holds when the body is witnessed, projecting the variable out"
      (is (v/ask? kb (list 'thereExists '?x (list 'parentOf '?x Tom))))
      (is (empty? (get (tu/sole-answer (v/ask kb (list 'thereExists '?x (list 'parentOf '?x Tom)))) '?x))
          "the quantified variable does not leak into the answer"))
    (testing "fails when nothing witnesses it"
      (is (not (v/ask? kb (list 'thereExists '?x (list 'parentOf '?x Nemo))))))))

(tu/deftest-kb unknown-combined-with-there-exists
  (tu/with-terms [parentOf Ann Tom Orphan]
    (v/assert kb (list 'parentOf Ann Tom) 'CxWell)
    (testing "(unknown (thereExists ...)) is 'nobody stands in the relation'"
      (is (v/ask? kb (list 'unknown (list 'thereExists '?x (list 'parentOf '?x Orphan))))
          "no known parent of Orphan")
      (is (not (v/ask? kb (list 'unknown (list 'thereExists '?x (list 'parentOf '?x Tom)))))
          "Tom has a known parent, so it is not unknown"))))

;; ---- neither is assertible ----------------------------------------------

(tu/deftest-kb naf-operators-are-not-assertible
  (tu/with-terms [flies Tweety]
    (testing "asserting a query operator as a fact is refused (it stores nothing)"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'unknown (list 'flies Tweety)) 'CxWell)))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'thereExists '?x (list 'flies '?x)) 'CxWell))))))

;; ---- unknown in a rule antecedent: derive-time blocking -----------------

(tu/deftest-kb unknown-antecedent-fires-and-blocks-at-derive-time
  (tu/with-terms [pp qq rr Aa Bb]
    ;; (pp ?x) & unknown(qq ?x) => (rr ?x)
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x))) (list 'rr '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list 'pp Aa) 'CxWell)          ; qq Aa absent -> fires
    (v/assert kb (list 'qq Bb) 'CxWell)          ; qq Bb present *before* pp Bb -> blocked
    (v/assert kb (list 'pp Bb) 'CxWell)
    (testing "fires when the NAF query is not derivable"
      (is (v/ask? kb (list 'rr Aa) 'CxWell)))
    (testing "does not fire when the NAF query holds at derive time"
      (is (not (v/ask? kb (list 'rr Bb) 'CxWell))))))

;; ---- order independence: block on late arrival, revive on retract -------

(tu/deftest-kb unknown-is-order-independent-block-then-revive
  (tu/with-terms [pp qq rr Aa]
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x))) (list 'rr '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list 'pp Aa) 'CxWell)
    (testing "derived while the NAF query is absent"
      (is (v/ask? kb (list 'rr Aa) 'CxWell)))
    (let [h (v/assert kb (list 'qq Aa) 'CxWell)]
      (testing "a later fact that satisfies the query blocks and sweeps the conclusion"
        (is (not (v/ask? kb (list 'rr Aa) 'CxWell)))
        (is (nil? (v/handle-of kb (list 'rr Aa) 'CxWell))
            "the conclusion is deleted, not merely disbelieved (garbage collection, not defeat)"))
      (v/retract! kb h)
      (testing "retracting it revives the conclusion by re-derivation"
        (is (v/ask? kb (list 'rr Aa) 'CxWell))))))

(tu/deftest-kb a-guarded-firing-over-monotonic-facts-confers-default
  ;; docs/reference.md D14.  Every write is :monotonic and nothing blocks the guard; the
  ;; rows run the fact before the rule and the rule before the fact.
  (tu/with-terms [pp qq rr Aa]
    (let [M      {:strength :monotonic}
          bare   (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x)))
          class  #(v/defeat-class kb (v/handle-of kb (list rr Aa) 'CxWell))]
      (doseq [[rule want] [[bare :monotonic]
                           [(list 'set/forwardRule
                                  (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                                        (list rr '?x)))
                            :default]
                           [(list 'exceptWhen (list qq '?x) bare) :default]]
              fact-first? [true false]]
        (let [hs (if fact-first?
                   [(v/assert kb (list pp Aa) 'CxWell M) (v/assert kb rule 'CxWell M)]
                   [(v/assert kb rule 'CxWell M) (v/assert kb (list pp Aa) 'CxWell M)])]
          (is (= want (class)) (pr-str rule (if fact-first? :fact-first :rule-first)))
          (run! #(v/retract! kb %) (reverse hs))))
      (testing "an exceptWhen stated after the firing lowers it, and its retraction restores it"
        (let [hr (v/assert kb bare 'CxWell M)
              hf (v/assert kb (list pp Aa) 'CxWell M)
              he (v/assert kb (list 'exceptWhen (list qq '?x) bare) 'CxWell M)]
          (is (= :default (class)))
          (v/retract! kb he)
          (is (= :monotonic (class)))
          (run! #(v/retract! kb %) [hf hr]))))))

(tu/deftest-kb unknown-is-order-independent-when-a-merge-is-what-arrives
  ;; A merge is the other way `S` becomes derivable, and it is not a fact arriving: the
  ;; inner query is answered under the term's **representative**, so `(unknown (qq Kept))`
  ;; is false for a firing that bound `?x` to a spelling the merge retired — with nothing
  ;; on `qq` having moved, so no predicate-keyed trigger can see it.
  ;;
  ;; `rewriteOf` rather than `sameAs` because the direction is the point: `sameAs` elects
  ;; by content, and if the `qq` fact's own term lost the election it would migrate, and
  ;; the migration would post an ordinary trigger that hides the channel under test.
  (tu/with-terms [pp qq rr Kept Retired]
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                       (list rr '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list qq Kept) 'CxWell)
    (v/assert kb (list pp Retired) 'CxWell)
    (is (v/ask? kb (list rr Retired) 'CxWell)
        "derived while nothing under qq reaches that individual")
    (let [h (v/assert kb (list 'rewriteOf Kept Retired) 'CxWell)]
      (testing "the merge makes the inner query derivable, so the conclusion is swept"
        (is (= 1 (count (v/sentexes-matching kb (list qq '?x) 'CxWell)))
            "and qq's own extent never moved")
        (is (empty? (v/sentexes-matching kb (list rr '?x) 'CxWell))
            "under either spelling — the conclusion migrated and then went"))
      (v/retract! kb h)
      (testing "and splitting the class again revives it"
        (is (v/ask? kb (list rr Retired) 'CxWell))))))

(tu/deftest-kb a-merge-can-complete-a-conjunction-through-the-conjunct-that-was-short
  ;; The conjunctive reading of the merge channel: `qq` holds of one spelling and `rr` of
  ;; the other, so under the firing's own binding the conjunction is one conjunct short
  ;; and the rule concludes.  Merging the two makes *both* answerable under one
  ;; representative — with nothing on either predicate arriving or leaving, so no
  ;; predicate-keyed trigger sees it and `recheck-equality-edge` is the whole channel.
  (tu/with-terms [pp qq rr ss Kept Retired]
    (v/assert kb (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                       (list ss '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list qq Kept) 'CxWell)
    (v/assert kb (list rr Retired) 'CxWell)
    (v/assert kb (list pp Retired) 'CxWell)
    (is (v/ask? kb (list ss Retired) 'CxWell)
        "derived while qq reaches Kept and the firing binds Retired")
    (let [h (v/assert kb (list 'rewriteOf Kept Retired) 'CxWell)]
      (testing "the merge answers both conjuncts under one representative, so it is swept"
        (is (= 1 (count (v/sentexes-matching kb (list qq '?x) 'CxWell)))
            "and qq's own extent never moved")
        (is (empty? (v/sentexes-matching kb (list ss '?x) 'CxWell))
            "under either spelling — the conclusion migrated and then went"))
      (v/retract! kb h)
      (testing "and splitting the class again revives it"
        (is (v/ask? kb (list ss Retired) 'CxWell))))))

(tu/deftest-kb a-conjunction-reaches-the-same-belief-when-the-merge-arrives-first
  ;; The oracle for the test above.  Merged first, the firing is refused at derive time
  ;; and no trigger is involved at all, so the two orders must agree.
  (tu/with-terms [pp qq rr ss Kept Retired]
    (v/assert kb (list 'rewriteOf Kept Retired) 'CxWell)
    (v/assert kb (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                       (list ss '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list qq Kept) 'CxWell)
    (v/assert kb (list rr Retired) 'CxWell)
    (v/assert kb (list pp Retired) 'CxWell)
    (is (empty? (v/sentexes-matching kb (list ss '?x) 'CxWell))
        "merged first, the rule never concludes")))

(tu/deftest-kb an-unknown-reaches-the-same-belief-when-the-merge-arrives-first
  ;; the oracle for the test above: merged first, the firing is refused at derive time
  ;; and no trigger is involved at all, so the two orders must agree.
  (tu/with-terms [pp qq rr Kept Retired]
    (v/assert kb (list 'rewriteOf Kept Retired) 'CxWell)
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                       (list rr '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list qq Kept) 'CxWell)
    (v/assert kb (list pp Retired) 'CxWell)
    (is (empty? (v/sentexes-matching kb (list rr '?x) 'CxWell))
        "merged first, the rule never concludes")))

(tu/deftest-kb unknown-with-there-exists-in-a-rule
  (tu/with-terms [person owns ownerless Zed]
    ;; a person nothing owns is ownerless
    (v/assert kb (list 'implies (list 'and (list 'person '?p)
                                      (list 'unknown (list 'thereExists '?c (list 'owns '?c '?p))))
                       (list 'ownerless '?p))
              'CxWell {:direction :forward})
    (v/assert kb (list 'person Zed) 'CxWell)
    (testing "holds while nothing witnesses the existential"
      (is (v/ask? kb (list 'ownerless Zed) 'CxWell)))
    (let [h (v/assert kb (list 'owns (tu/tmp-ind "Hat") Zed) 'CxWell)]
      (testing "a witness blocks it"
        (is (not (v/ask? kb (list 'ownerless Zed) 'CxWell))))
      (v/retract! kb h)
      (testing "removing the witness revives it"
        (is (v/ask? kb (list 'ownerless Zed) 'CxWell))))))

(tu/deftest-kb standalone-there-exists-antecedent-is-a-parent
  (tu/with-terms [person parentOf a_parent Dad Kid Childless]
    ;; positive existential antecedent: a person with a child is a parent
    (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                      (list 'thereExists '?y (list 'parentOf '?x '?y)))
                       (list 'a_parent '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list 'human Dad) 'CxWell)
    (v/assert kb (list 'person Childless) 'CxWell)
    (v/assert kb (list 'parentOf Dad Kid) 'CxWell)
    (testing "fires for a witnessed existential, not for an unwitnessed one"
      (is (v/ask? kb (list 'a_parent Dad) 'CxWell))
      (is (not (v/ask? kb (list 'a_parent Childless) 'CxWell))))))

;; ---- a conjunctive NAF query --------------------------------------------
;; `(unknown (and A B))` is `exceptWhen`'s conjunction inlined per literal: closure
;; leaves every conjunct ground, so they share nothing after substitution and each is an
;; independent existence check — block if **all** hold.  One evaluator answers both
;; (`provers/exception-holds?`), so the two cannot drift.

(tu/deftest-kb unknown-over-a-conjunction-blocks-only-when-every-conjunct-holds
  (tu/with-terms [pp qq rr ss Both One Neither]
    (v/assert kb (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                       (list ss '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list qq Both) 'CxWell)
    (v/assert kb (list rr Both) 'CxWell)
    (v/assert kb (list qq One) 'CxWell)
    (doseq [i [Both One Neither]] (v/assert kb (list pp i) 'CxWell))
    (testing "every conjunct derivable — the query holds, so the firing is blocked"
      (is (not (v/ask? kb (list ss Both) 'CxWell))))
    (testing "one conjunct short is not the query holding"
      (is (v/ask? kb (list ss One) 'CxWell))
      (is (v/ask? kb (list ss Neither) 'CxWell)))))

(tu/deftest-kb every-conjunct-of-a-NAF-query-is-watched
  ;; The re-check index is keyed per predicate, and a conjunction blocks on the *last*
  ;; of its conjuncts to arrive — so a rule posted under the first predicate alone would
  ;; never be re-checked for the second, and belief would depend on arrival order.
  (tu/with-terms [pp qq rr ss Aa]
    (v/assert kb (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                       (list ss '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list pp Aa) 'CxWell)
    (v/assert kb (list qq Aa) 'CxWell)
    (is (v/ask? kb (list ss Aa) 'CxWell)
        "one conjunct holding leaves the query underivable")
    (let [h (v/assert kb (list rr Aa) 'CxWell)]      ; the *second* conjunct, last
      (testing "completing the conjunction blocks and sweeps the conclusion"
        (is (not (v/ask? kb (list ss Aa) 'CxWell)))
        (is (nil? (v/handle-of kb (list ss Aa) 'CxWell))))
      (v/retract! kb h)
      (testing "and breaking it again revives the conclusion by re-derivation"
        (is (v/ask? kb (list ss Aa) 'CxWell))))))

(tu/deftest-kb a-conjunctive-NAF-goal-agrees-with-the-rule-antecedent
  ;; The backward reading of the same query: `UnknownProver` answers a conjunction the
  ;; way `exception-holds?` does, or `ask` and forward chaining would disagree about one
  ;; rule.
  (tu/with-terms [qq rr Both One]
    (v/assert kb (list qq Both) 'CxWell)
    (v/assert kb (list rr Both) 'CxWell)
    (v/assert kb (list qq One) 'CxWell)
    (is (not (v/ask? kb (list 'unknown (list 'and (list qq Both) (list rr Both)))))
        "both conjuncts derivable — the conjunction is known")
    (is (v/ask? kb (list 'unknown (list 'and (list qq One) (list rr One))))
        "one conjunct short — the conjunction is not derivable")))

(tu/deftest-kb a-nested-NAF-conjunction-is-flattened-not-left-as-a-goal
  ;; A nested `and` is not a goal any prover claims, so left as one conjunct it would come
  ;; back unanswerable and read as *not derivable* — the conjunction never holding, the
  ;; antecedent guarding nothing.  Conjunction is associative, so flattening is the
  ;; reading; the canonical form is flat, which is what makes the two spellings one rule.
  (tu/with-terms [pp qq rr tt ss All]
    (let [nested (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x)
                                                           (list 'and (list rr '?x)
                                                                 (list tt '?x)))))
                       (list ss '?x))
          flat   (list 'implies (list 'and (list pp '?y)
                                      (list 'unknown (list 'and (list qq '?y) (list rr '?y)
                                                           (list tt '?y))))
                       (list ss '?y))
          h1     (v/assert kb nested 'CxWell)
          h2     (v/assert kb flat 'CxWell)]
      (is (= h1 h2) "the nested spelling and the flat one are one rule")
      (doseq [p [pp qq rr tt]] (v/assert kb (list p All) 'CxWell))
      (is (not (v/ask? kb (list ss All) 'CxWell))
          "every conjunct of the flattened query holds, so the firing is blocked"))))

(tu/deftest-kb a-thereExists-conjunct-is-watched-by-what-it-quantifies
  ;; A conjunct may itself be an existential — legal, because the binder is local to that
  ;; one conjunct, so the conjuncts still share nothing.  The re-check key has to be the
  ;; predicate *inside* the quantifier (`watched-query` per conjunct): keyed on
  ;; `thereExists`, which no fact carries, the arrival that completes the query is invisible.
  (tu/with-terms [person kidOf adult lonely Ppp Qqq]
    (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                      (list 'unknown
                                            (list 'and (list 'thereExists '?c (list kidOf '?x '?c))
                                                  (list adult '?x))))
                       (list lonely '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list 'person Ppp) 'CxWell)
    (v/assert kb (list adult Ppp) 'CxWell)
    (is (v/ask? kb (list lonely Ppp) 'CxWell)
        "adult but childless — the existential conjunct is short, so the query does not hold")
    (let [h (v/assert kb (list kidOf Ppp Qqq) 'CxWell)]
      (testing "a witness arriving completes the query through the *existential* conjunct"
        (is (not (v/ask? kb (list lonely Ppp) 'CxWell))))
      (v/retract! kb h)
      (testing "and removing it revives the conclusion"
        (is (v/ask? kb (list lonely Ppp) 'CxWell))))))

(tu/deftest-kb a-conjunctive-NAF-antecedent-is-honoured-by-a-backward-only-rule
  ;; The companion of the single-literal case below: a backward-only rule is never
  ;; pre-materialized, so whoever expands it evaluates the conjunction itself.
  (tu/with-terms [pp qq rr ss Both One]
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list pp '?x)
                                            (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                             (list ss '?x)))
              'CxWell)
    (v/assert kb (list pp Both) 'CxWell)
    (v/assert kb (list qq Both) 'CxWell)
    (v/assert kb (list rr Both) 'CxWell)
    (v/assert kb (list pp One) 'CxWell)
    (v/assert kb (list qq One) 'CxWell)
    (is (empty? (v/prove kb (list ss Both) 'CxWell))
        "both conjuncts derivable — the rule does not conclude")
    (is (seq (v/prove kb (list ss One) 'CxWell))
        "one conjunct short — it does")))

(tu/deftest-kb a-negated-conjunct-is-watched-and-blocks-when-it-arrives
  ;; `not` is the one frame the watched-predicate walk leaves alone, because the trigger
  ;; side keys an arriving `(not S)` under `not` as well — coarse, one bucket for every
  ;; negated condition, but the two agree, and peeling one side alone is what would break
  ;; it.  The claim is the arrival, so this is the test that would catch a peel.
  (tu/with-terms [bb ff aa oo Ned]
    (v/assert kb (list 'implies (list 'and (list bb '?x)
                                      (list 'unknown (list 'and (list 'not (list ff '?x))
                                                           (list aa '?x))))
                       (list oo '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list bb Ned) 'CxWell)
    (v/assert kb (list aa Ned) 'CxWell)
    (is (v/ask? kb (list oo Ned) 'CxWell)
        "the negated conjunct is not derivable, so the conjunction is short")
    (v/assert kb (list 'not (list ff Ned)) 'CxWell)
    (is (not (v/ask? kb (list oo Ned) 'CxWell))
        "and its arrival completes the query, so the conclusion is swept")))

(tu/deftest-kb an-aggregate-conjunct-is-watched-by-its-census-body
  ;; An aggregate's own functor is a predicate no fact carries, so the key has to be what
  ;; its body counts — the per-conjunct case of what `naf-predicates` has always done for
  ;; a bare aggregate query.
  (tu/with-terms [person kidOf adult gg Moe K1 K2]
    (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                      (list 'unknown
                                            (list 'and (list 'agg/count 2 '?c (list kidOf '?x '?c))
                                                  (list adult '?x))))
                       (list gg '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list 'person Moe) 'CxWell)
    (v/assert kb (list adult Moe) 'CxWell)
    (v/assert kb (list kidOf Moe K1) 'CxWell)
    (is (v/ask? kb (list gg Moe) 'CxWell)
        "one kid — the census is not 2, so the conjunction is short")
    (v/assert kb (list kidOf Moe K2) 'CxWell)
    (is (not (v/ask? kb (list gg Moe) 'CxWell))
        "the count reaching 2 completes the query, on a predicate the aggregate frames")))

(tu/deftest-kb conjunct-order-is-not-a-NAF-rule-s-identity
  ;; The claim `sort-conjuncts` makes for an exceptWhen exception, and for the same
  ;; reason: independent ground checks, so their written order is not their identity.
  (tu/with-terms [pp qq rr ss]
    (let [h1 (v/assert kb (list 'implies (list 'and (list pp '?x)
                                               (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                                (list ss '?x))
                       'CxWell {:direction :forward})
          h2 (v/assert kb (list 'implies (list 'and (list pp '?y)
                                               (list 'unknown (list 'and (list rr '?y) (list qq '?y))))
                                (list ss '?y))
                       'CxWell {:direction :forward})
          h3 (v/assert kb (list 'implies (list 'and (list pp '?z)
                                               (list 'unknown (list 'and (list qq '?z) (list rr '?z)
                                                                    (list qq '?z))))
                                (list ss '?z))
                       'CxWell {:direction :forward})]
      (is (= h1 h2) "two spellings of one conjunction are one rule")
      (is (= h1 h3) "and a repeated conjunct is not a different condition"))))

(tu/deftest-kb a-one-conjunct-NAF-and-loses-the-and-it-never-needed
  (tu/with-terms [mm nn zz]
    (let [h1 (v/assert kb (list 'implies (list 'and (list mm '?x)
                                               (list 'unknown (list 'and (list nn '?x))))
                                (list zz '?x))
                       'CxWell {:direction :forward})
          h2 (v/assert kb (list 'implies (list 'and (list mm '?y) (list 'unknown (list nn '?y)))
                                (list zz '?y))
                       'CxWell {:direction :forward})]
      (is (= h1 h2) "a lone conjunct is the bare literal, and stores as it"))))

;; ---- well-formedness of NAF rule antecedents ----------------------------

(tu/deftest-kb an-aggregate-refuses-a-reduction-variable-no-census-conjunct-produces
  ;; A census body is joined like a NAF query, so its conjuncts share `?v` — but the join
  ;; runs generators first, so a `?v` only a *computed* conjunct reads is a count over a
  ;; variable nothing in the body can bind.  The same hole an `unknown` is refused for.
  (tu/with-terms [person childOf sick counted]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"which no conjunct of it binds"
         (v/assert kb (list 'implies
                            (list 'and (list person '?x)
                                  (list 'agg/count '?n '?c (list 'and (list childOf '?x '?x)
                                                                 (list 'unknown (list sick '?c))))
                                  (list 'lessThan 1 '?n))
                            (list counted '?x))
                   'CxWell {:direction :forward})))
    (testing "and the same body with a generator binding it is admitted"
      (is (some? (v/assert kb (list 'implies
                                    (list 'and (list person '?x)
                                          (list 'agg/count '?n '?c
                                                (list 'and (list childOf '?x '?c)
                                                      (list sick '?c)))
                                          (list 'lessThan 1 '?n))
                                    (list counted '?x))
                           'CxWell {:direction :forward}))))))

;; ---- the joined NAF query: conjuncts sharing a quantifier's variable ----

(tu/deftest-kb a-quantified-conjunction-takes-one-witness-for-all-its-conjuncts
  ;; The whole point of the join: "has no sick child" must not hold of a parent whose
  ;; child is well merely because *some other* individual is sick.
  (tu/with-terms [childOf sick Tom Kid Stranger]
    (v/assert kb (list childOf Tom Kid) 'CxWell)
    (v/assert kb (list sick Stranger) 'CxWell)
    (let [q (list 'unknown (list 'thereExists '?c (list 'and (list childOf Tom '?c)
                                                        (list sick '?c))))]
      (testing "a well child and a sick stranger leave the existential unsatisfied"
        (is (v/ask? kb q 'CxWell)
            "read flat, the two conjuncts would each find their own witness and this would fail"))
      (v/assert kb (list sick Kid) 'CxWell)
      (testing "and the same child being sick is what satisfies it"
        (is (not (v/ask? kb q 'CxWell)))))))

(tu/deftest-kb a-joined-NAF-antecedent-blocks-and-revives
  (tu/with-terms [person childOf sick unworried Tom Kid]
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'unknown (list 'thereExists '?c
                                                  (list 'and (list childOf '?x '?c)
                                                        (list sick '?c)))))
                       (list unworried '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list person Tom) 'CxWell)
    (v/assert kb (list childOf Tom Kid) 'CxWell)
    (testing "no sick child, so the rule fires"
      (is (v/ask? kb (list unworried Tom) 'CxWell)))
    (let [h (v/assert kb (list sick Kid) 'CxWell)]
      (testing "the *second* conjunct's predicate is watched too, so the firing is swept"
        (is (not (v/ask? kb (list unworried Tom) 'CxWell)))
        (is (nil? (v/handle-of kb (list unworried Tom) 'CxWell))))
      (v/retract! kb h)
      (testing "and retracting it revives the conclusion by re-derivation"
        (is (v/ask? kb (list unworried Tom) 'CxWell))))))

(tu/deftest-kb a-joined-NAF-antecedent-is-order-independent
  ;; The same knowledge in the other order: the sick child is there before the rule is.
  (tu/with-terms [person childOf sick unworried Tom Kid]
    (v/assert kb (list person Tom) 'CxWell)
    (v/assert kb (list childOf Tom Kid) 'CxWell)
    (v/assert kb (list sick Kid) 'CxWell)
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'unknown (list 'thereExists '?c
                                                  (list 'and (list childOf '?x '?c)
                                                        (list sick '?c)))))
                       (list unworried '?x))
              'CxWell {:direction :forward})
    (is (not (v/ask? kb (list unworried Tom) 'CxWell))
        "the rule never fires, which is the answer the other arrival order settles on")))

(tu/deftest-kb every-conjunct-of-a-quantified-query-is-a-negative-edge
  ;; Stratification reads the conjuncts through the quantifier, so a cycle through the
  ;; *second* one is refused as readily as one through the first.
  (tu/with-terms [person childOf sick unworried]
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'unknown (list 'thereExists '?c
                                                  (list 'and (list childOf '?x '?c)
                                                        (list sick '?c)))))
                       (list unworried '?x))
              'CxWell {:direction :forward})
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"not stratified"
         (v/assert kb (list 'implies (list unworried '?y) (list sick '?y)) 'CxWell {:direction :forward})))))

(tu/deftest-kb a-standalone-existential-over-a-conjunction-is-the-join-written-out
  ;; A *positive* standalone `thereExists` needs no NAF machinery: its conjunction is
  ;; spliced in as that many antecedents, which is the join a reader would have written.
  (tu/with-terms [parentOf sick worried Ann Kid]
    (let [h1 (v/assert kb (list 'implies
                                (list 'and (list 'thereExists '?c
                                                 (list 'and (list parentOf '?x '?c)
                                                       (list sick '?c))))
                                (list worried '?x))
                       'CxWell {:direction :forward})
          h2 (v/assert kb (list 'implies (list 'and (list parentOf '?p '?k) (list sick '?k))
                                (list worried '?p))
                       'CxWell {:direction :forward})]
      (is (= h1 h2) "the desugared rule is the hand-written join, to the same handle"))
    (v/assert kb (list parentOf Ann Kid) 'CxWell)
    (v/assert kb (list sick Kid) 'CxWell)
    (is (v/ask? kb (list worried Ann) 'CxWell))))

;; ---- a closed extent: (not (P a)) read as negation as failure ----------

(tu/deftest-kb a-closed-extent-answers-the-negative-from-the-absence-of-a-positive
  ;; "the months of the year are exactly these twelve"
  (tu/with-terms [month_of_year January February Smarch CxCalendar CxSibling]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSibling 'CxUniverse) 'CxUniverse)
    (v/assert kb (list month_of_year January) CxCalendar)
    (v/assert kb (list month_of_year February) CxCalendar)
    (testing "without the grant, a month nobody listed is merely unknown"
      (is (not (v/ask? kb (list 'not (list month_of_year Smarch)) CxCalendar))))
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (testing "under the grant, nothing answering the positive is what answers the negative"
      (is (v/ask? kb (list 'not (list month_of_year Smarch)) CxCalendar))
      (is (not (v/ask? kb (list 'not (list month_of_year January)) CxCalendar))
          "a member is not refuted by its own extent"))
    (testing "and the grant is scoped: a sibling theory reading the same predicate
              answers as it did before"
      (is (not (v/ask? kb (list 'not (list month_of_year Smarch)) CxSibling))))
    (testing "a member arriving withdraws the negative"
      (let [h (v/assert kb (list month_of_year Smarch) CxCalendar)]
        (is (not (v/ask? kb (list 'not (list month_of_year Smarch)) CxCalendar)))
        (v/retract! kb h)
        (is (v/ask? kb (list 'not (list month_of_year Smarch)) CxCalendar))))))

(tu/deftest-kb a-closed-extent-rule-antecedent-is-negation-as-failure
  (tu/with-terms [month_of_year candidate not_a_month Smarch CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                      (list 'not (list month_of_year '?m)))
                       (list not_a_month '?m))
              CxCalendar {:direction :forward})
    (v/assert kb (list candidate Smarch) CxCalendar)
    (testing "the rule fires on the absence of a member, with nothing negative stored"
      (is (v/ask? kb (list not_a_month Smarch) CxCalendar))
      (is (nil? (v/handle-of kb (list 'not (list month_of_year Smarch)) CxCalendar))
          "and nothing about the negative space was stored to make it fire"))
    (let [h (v/assert kb (list month_of_year Smarch) CxCalendar)]
      (testing "the member arriving withdraws the firing"
        (is (not (v/ask? kb (list not_a_month Smarch) CxCalendar)))
        (is (nil? (v/handle-of kb (list not_a_month Smarch) CxCalendar))
            "withdrawn, not merely disbelieved"))
      (v/retract! kb h)
      (testing "and retracting it revives the conclusion"
        (is (v/ask? kb (list not_a_month Smarch) CxCalendar))))))

(tu/deftest-kb a-closed-extent-rule-is-order-independent
  ;; The same knowledge in the other order: the member is there before the rule and
  ;; before the grant.
  (tu/with-terms [month_of_year candidate not_a_month Smarch CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list candidate Smarch) CxCalendar)
    (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                      (list 'not (list month_of_year '?m)))
                       (list not_a_month '?m))
              CxCalendar {:direction :forward})
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (testing "the grant arriving after the rule is what makes it fire"
      (is (v/ask? kb (list not_a_month Smarch) CxCalendar)))
    (v/assert kb (list month_of_year Smarch) CxCalendar)
    (testing "and a member arriving after that withdraws it, as in the other order"
      (is (not (v/ask? kb (list not_a_month Smarch) CxCalendar))))))

(tu/deftest-kb a-stored-negative-still-works-under-a-closed-extent
  (tu/with-terms [month_of_year candidate not_a_month Smarch CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                      (list 'not (list month_of_year '?m)))
                       (list not_a_month '?m))
              CxCalendar {:direction :forward})
    (v/assert kb (list candidate Smarch) CxCalendar)
    (v/assert kb (list 'not (list month_of_year Smarch)) CxCalendar)
    (is (v/ask? kb (list not_a_month Smarch) CxCalendar)
        "a stored negative answers the antecedent as it always did")))

(tu/deftest-kb a-closed-extent-cycle-through-negation-is-refused
  (tu/with-terms [month_of_year candidate CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (testing "a rule concluding P whose body reads (not (P …)) under the grant"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                             (list 'not (list month_of_year '?m)))
                              (list month_of_year '?m))
                     CxCalendar {:direction :forward}))))))

(tu/deftest-kb a-grant-that-would-close-a-cycle-is-refused
  ;; The other arrival order: the rule is stored first, and the grant is what would add
  ;; the negative edge.
  (tu/with-terms [month_of_year candidate CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                      (list 'not (list month_of_year '?m)))
                       (list month_of_year '?m))
              CxCalendar {:direction :forward})
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"not stratified"
         (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)))))

(tu/deftest-kb why-not-says-the-extent-is-closed
  (tu/with-terms [month_of_year Smarch CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (testing "without the grant it is simply not stored"
      (is (= :not-stored (:reason (v/why-not kb (list month_of_year Smarch) CxCalendar)))))
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (testing "under it the KB is not silent — the extent is complete and this is not in it"
      (is (= :closed-extent
             (:reason (v/why-not kb (list month_of_year Smarch) CxCalendar)))))))

;; ---- a closed extent per argument: closedExtentForArg -------------------

(tu/deftest-kb a-per-argument-closed-extent-closes-only-the-named-value
  ;; "the accounts on HostA are exactly the stored ones"
  (tu/with-terms [accountOn Alice Carol HostA HostB CxHosts]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list accountOn Alice HostA) CxHosts)
    (testing "without the grant, an account nobody listed is merely unknown"
      (is (not (v/ask? kb (list 'not (list accountOn Carol HostA)) CxHosts))))
    (v/assert kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts)
    (testing "under the grant, nothing answering the positive is what answers the negative"
      (is (v/ask? kb (list 'not (list accountOn Carol HostA)) CxHosts))
      (is (v/ask? kb (list accountOn Alice HostA) CxHosts))
      (is (not (v/ask? kb (list 'not (list accountOn Alice HostA)) CxHosts))
          "a member is not refuted by its own extent"))
    (testing "a goal whose argument 2 is another value stays open-world"
      (is (not (v/ask? kb (list 'not (list accountOn Carol HostB)) CxHosts))))))

(tu/deftest-kb the-binary-sugar-derives-the-ternary-grant
  (tu/with-terms [accountOn Alice Carol HostA HostB CxHosts]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list accountOn Alice HostA) CxHosts)
    (v/assert kb (list 'closedExtentForArg2 accountOn HostA) CxHosts)
    (testing "the sugar derives the ternary"
      (is (v/ask? kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts)))
    (testing "and reads exactly as the ternary does"
      (is (v/ask? kb (list 'not (list accountOn Carol HostA)) CxHosts))
      (is (v/ask? kb (list accountOn Alice HostA) CxHosts))
      (is (not (v/ask? kb (list 'not (list accountOn Carol HostB)) CxHosts))))))

(tu/deftest-kb a-per-argument-closed-extent-is-scoped-to-its-context
  (tu/with-terms [accountOn Alice Carol HostA CxHosts CxSibling]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSibling 'CxUniverse) 'CxUniverse)
    (v/assert kb (list accountOn Alice HostA) 'CxUniverse)
    (v/assert kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts)
    (is (v/ask? kb (list 'not (list accountOn Carol HostA)) CxHosts))
    (is (not (v/ask? kb (list 'not (list accountOn Carol HostA)) CxSibling))
        "a sibling theory without the grant answers open-world")))

(tu/deftest-kb a-per-argument-closed-extent-follows-belief
  (tu/with-terms [accountOn Alice HostA CxHosts]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts)
    (let [h (v/assert kb (list accountOn Alice HostA) CxHosts)]
      (is (not (v/ask? kb (list 'not (list accountOn Alice HostA)) CxHosts)))
      (v/retract! kb h)
      (is (v/ask? kb (list 'not (list accountOn Alice HostA)) CxHosts)
          "a retracted member leaves the extent, and the negative holds"))))

(tu/deftest-kb a-per-argument-closed-extent-needs-the-position-ground
  (tu/with-terms [accountOn Alice HostA CxHosts]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list accountOn Alice HostA) CxHosts)
    (v/assert kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts)
    (is (empty? (v/ask kb (list 'not (list accountOn Alice '?host)) CxHosts))
        "an open argument 2 is a search over the complement, which the grant does not license")))

(tu/deftest-kb a-per-argument-closed-extent-rule-antecedent-is-negation-as-failure
  (tu/with-terms [accountOn candidate unknown_on_host Carol HostA CxHosts]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts)
    (v/assert kb (list 'implies (list 'and (list candidate '?u)
                                      (list 'not (list accountOn '?u HostA)))
                       (list unknown_on_host '?u))
              CxHosts {:direction :forward})
    (v/assert kb (list candidate Carol) CxHosts)
    (testing "the rule fires on the absence of an account, with nothing negative stored"
      (is (v/ask? kb (list unknown_on_host Carol) CxHosts)))
    (v/assert kb (list accountOn Carol HostA) CxHosts)
    (testing "the account arriving withdraws the firing"
      (is (not (v/ask? kb (list unknown_on_host Carol) CxHosts))))))

(tu/deftest-kb a-per-argument-closed-extent-cycle-through-negation-is-refused
  (tu/with-terms [accountOn candidate HostA CxHosts]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts)
    (testing "a rule concluding P whose body reads (not (P …)) under the grant"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'and (list candidate '?u)
                                             (list 'not (list accountOn '?u HostA)))
                              (list accountOn '?u HostA))
                     CxHosts {:direction :forward}))))))

(tu/deftest-kb a-per-argument-grant-that-would-close-a-cycle-is-refused
  ;; The other arrival order: the rule is stored first, and the grant is what would add
  ;; the negative edge.
  (tu/with-terms [accountOn candidate HostA CxHosts]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list candidate '?u)
                                      (list 'not (list accountOn '?u HostA)))
                       (list accountOn '?u HostA))
              CxHosts {:direction :forward})
    (testing "the ternary grant"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts))))
    (testing "and its binary sugar"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'closedExtentForArg2 accountOn HostA) CxHosts))))))

(tu/deftest-kb a-whole-closure-entails-every-per-argument-closure-inertly
  (let [r '(implies (and (closed_extent_predicate ?pred) (admitsArgnum ?pred ?position)
                         (thing ?value))
                    (closedExtentForArg ?pred ?position ?value))
        h (v/handle-of kb (list 'set/inertRule r) 'CxCore)]
    (testing "the defining rule is stored in CxCore, believed, and run by neither engine"
      (is (some? h))
      (is (v/in? kb h))
      (is (= #{} (:engines (v/sentex kb h)))))
    (tu/with-terms [accountOn Alice HostA CxHosts]
      (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'binary_predicate accountOn) CxHosts)
      (v/assert kb (list accountOn Alice HostA) CxHosts)
      (v/assert kb (list 'closed_extent_predicate accountOn) CxHosts)
      (is (empty? (v/sentexes-matching kb (list 'closedExtentForArg accountOn '?n '?v) CxHosts))
          "a whole-predicate grant stores no per-argument grant"))))

(tu/deftest-kb why-not-says-the-extent-is-closed-for-the-argument
  (tu/with-terms [accountOn Carol HostA HostB CxHosts]
    (v/assert kb (list 'genlCx CxHosts 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closedExtentForArg accountOn 2 HostA) CxHosts)
    (is (= :closed-extent (:reason (v/why-not kb (list accountOn Carol HostA) CxHosts))))
    (is (= :not-stored (:reason (v/why-not kb (list accountOn Carol HostB) CxHosts)))
        "another value of the argument is simply not stored")))

;; ---- forall: sugar for the nested NAF ----------------------------------

(deftest forall-desugars-to-a-nested-unknown
  (testing "forall ?y (B => H) is not-exists ?y (B and not-H), two unknowns in a closed world"
    (is (= '(unknown (thereExists ?y (and (childOf ?x ?y) (unknown (asleep ?y)))))
           (sx/desugar-forall-literal '(forall ?y (implies (childOf ?x ?y) (asleep ?y)))))))
  (testing "a conjunctive body contributes that many conjuncts to the join"
    (is (= '(unknown (thereExists ?y (and (childOf ?x ?y) (minor ?y) (unknown (asleep ?y)))))
           (sx/desugar-forall-literal
            '(forall ?y (implies (and (childOf ?x ?y) (minor ?y)) (asleep ?y)))))))
  (testing "a forall over something that is not an implication is refused"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not an \(implies"
                          (sx/desugar-forall-literal '(forall ?y (asleep ?y))))))
  (testing "free-vars subtracts the binder, so a closed forall is closed"
    (is (= '#{?x} (sx/free-vars '(forall ?y (implies (childOf ?x ?y) (asleep ?y))))))))

(tu/deftest-kb a-stored-forall-rule-shows-the-nested-form
  (tu/with-terms [person childOf asleep all_kids_asleep]
    (let [sugar (list 'implies
                      (list 'and (list person '?x)
                            (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                    (list asleep '?y))))
                      (list all_kids_asleep '?x))
          nested (list 'implies
                       (list 'and (list person '?p)
                             (list 'unknown
                                   (list 'thereExists '?k
                                         (list 'and (list childOf '?p '?k)
                                               (list 'unknown (list asleep '?k))))))
                       (list all_kids_asleep '?p))]
      (is (= (:sentence (v/canonical-sentex kb sugar 'CxWell))
             (:sentence (v/canonical-sentex kb nested 'CxWell)))
          "the sugar exists at the entry point and nowhere past it")
      (is (= (v/assert kb sugar 'CxWell) (v/assert kb nested 'CxWell))
          "so the two are one rule, to one handle"))))

(tu/deftest-kb all-of-bobs-children-are-asleep
  ;; The common-sense reading, in the order the classical one is argued in.
  (tu/with-terms [person childOf asleep all_kids_asleep Bob Kid1 Kid2 Kid3]
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                     (list asleep '?y))))
                       (list all_kids_asleep '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list person Bob) 'CxWell)
    (testing "vacuously true - Bob has no children, so nothing is a counterexample"
      (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))
    (v/assert kb (list childOf Bob Kid1) 'CxWell)
    (v/assert kb (list asleep Kid1) 'CxWell)
    (v/assert kb (list childOf Bob Kid2) 'CxWell)
    (v/assert kb (list asleep Kid2) 'CxWell)
    (testing "two children, both asleep"
      (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))
    (let [h (v/assert kb (list childOf Bob Kid3) 'CxWell)]
      (testing "a third child nobody says is asleep is the counterexample"
        (is (not (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))
        (is (nil? (v/handle-of kb (list all_kids_asleep Bob) 'CxWell))
            "the conclusion is withdrawn, not merely disbelieved"))
      (testing "and the goal form agrees with the rule antecedent"
        (is (not (v/ask? kb (list 'forall '?y (list 'implies (list childOf Bob '?y)
                                                    (list asleep '?y)))
                         'CxWell))))
      (v/retract! kb h)
      (testing "retracting that child revives the conclusion"
        (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell))))
    (testing "and the third child back, asleep, is not a counterexample"
      (v/assert kb (list childOf Bob Kid3) 'CxWell)
      (v/assert kb (list asleep Kid3) 'CxWell)
      (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))))

(tu/deftest-kb forall-is-order-independent
  ;; The counterexample is already there when the rule arrives.
  (tu/with-terms [person childOf asleep all_kids_asleep Bob Kid1]
    (v/assert kb (list person Bob) 'CxWell)
    (v/assert kb (list childOf Bob Kid1) 'CxWell)
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                     (list asleep '?y))))
                       (list all_kids_asleep '?x))
              'CxWell {:direction :forward})
    (is (not (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))
    (v/assert kb (list asleep Kid1) 'CxWell)
    (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell)
        "and the same knowledge in either order settles the same way")))

(tu/deftest-kb a-forall-over-what-the-rule-concludes-is-a-cycle-through-negation
  ;; Both halves of the desugar are negative edges: the body's predicate and the head's.
  (tu/with-terms [person childOf asleep all_kids_asleep]
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                     (list asleep '?y))))
                       (list all_kids_asleep '?x))
              'CxWell {:direction :forward})
    (testing "a rule concluding the forall's head predicate closes the cycle"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list all_kids_asleep '?z) (list asleep '?z)) 'CxWell {:direction :forward}))))
    (testing "and so does one concluding its body predicate"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list all_kids_asleep '?z) (list childOf '?z '?z))
                     'CxWell {:direction :forward}))))))

(tu/deftest-kb a-forall-binder-that-escapes-is-refused
  (tu/with-terms [person childOf asleep flagged]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"escapes its quantifier"
         (v/assert kb (list 'implies
                            (list 'and (list person '?x) (list asleep '?y)
                                  (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                          (list asleep '?y))))
                            (list flagged '?x))
                   'CxWell {:direction :forward})))))

(tu/deftest-kb forall-is-not-assertible
  (tu/with-terms [childOf asleep Bob Kid]
    (testing "the written spelling binds its variable, so it is closed and reaches the query-operator arm"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"query operator"
           (v/assert kb (list 'forall '?y (list 'implies (list childOf Bob '?y)
                                                (list asleep '?y)))
                     'CxWell))))
    (testing "and a ground one reaches the query-operator arm, like unknown's"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"query operator"
           (v/assert kb (list 'forall Kid (list 'implies (list childOf Bob Kid)
                                                (list asleep Kid)))
                     'CxWell))))))

(tu/deftest-kb a-computed-conjunct-nothing-in-the-query-binds-is-refused
  (tu/with-terms [person childOf asleep settled]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"nothing in the query binds"
         (v/assert kb (list 'implies
                            (list 'and (list person '?x)
                                  (list 'unknown (list 'thereExists '?c
                                                       (list 'and (list childOf '?x '?x)
                                                             (list 'unknown (list asleep '?c))))))
                            (list settled '?x))
                   'CxWell {:direction :forward})))))

(tu/deftest-kb an-empty-NAF-conjunction-is-refused
  (tu/with-terms [person nobody]
    (testing "nothing can make it derivable, so it would guard nothing"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"empty conjunction"
           (v/assert kb (list 'implies (list 'and (list person '?x) (list 'unknown (list 'and)))
                              (list nobody '?x))
                     'CxWell {:direction :forward}))))))

(tu/deftest-kb unknown-must-be-closed-by-the-generators
  (tu/with-terms [person likes knows loner]
    (testing "an unknown whose free variable no generator binds is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not closed"
           (v/assert kb (list 'implies (list 'and (list 'person '?x) (list 'unknown (list 'likes '?x '?z)))
                              (list 'loner '?x))
                     'CxWell {:direction :forward}))))
    (testing "and so is a conjunction one of whose conjuncts is open — closure is what
              makes the conjuncts independent ground checks"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not closed"
           (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                             (list 'unknown (list 'and (list knows '?x)
                                                                  (list likes '?x '?z))))
                              (list 'loner '?x))
                     'CxWell {:direction :forward}))))))

(tu/deftest-kb there-exists-variable-must-be-local
  (tu/with-terms [person foo bar]
    (testing "a quantified variable that escapes its thereExists is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"escapes its quantifier"
           (v/assert kb (list 'implies (list 'and (list 'person '?x) (list 'thereExists '?x (list 'foo '?x)))
                              (list 'bar '?x))
                     'CxWell {:direction :forward}))))))

;; ---- stratification: no cycle through negation --------------------------

(tu/deftest-kb a-cycle-through-unknown-is-refused
  (tu/with-terms [aa bb cc dd ee]
    (testing "an acyclic NAF rule is accepted"
      (is (v/assert kb (list 'implies (list 'and (list 'aa '?x) (list 'unknown (list 'bb '?x)))
                             (list 'cc '?x))
                    'CxWell {:direction :forward})))
    (testing "closing the loop — a rule concluding the NAF predicate — is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'cc '?x) (list 'bb '?x)) 'CxWell {:direction :forward}))))
    (testing "a one-rule cycle (unknown on what it concludes) is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'and (list 'dd '?x) (list 'unknown (list 'ee '?x)))
                              (list 'ee '?x))
                     'CxWell {:direction :forward}))))))

(tu/deftest-kb a-cycle-through-any-conjunct-of-a-NAF-conjunction-is-refused
  ;; Every conjunct is a negative dependency, not just the first: the negative edges are
  ;; drawn from `rules/naf-predicates`, which reads the whole conjunction, so a rule
  ;; concluding *any* conjunct's predicate closes a cycle through negation.  Keyed on the
  ;; conjunction's own functor instead, the check would see one predicate — `and`, which
  ;; nothing concludes — and refuse nothing at all.
  (tu/with-terms [gg aa bb cc]
    (is (v/assert kb (list 'implies (list 'and (list gg '?x)
                                          (list 'unknown (list 'and (list aa '?x) (list bb '?x))))
                           (list cc '?x))
                  'CxWell {:direction :forward})
        "the acyclic conjunctive rule is accepted")
    (testing "closing the loop through the first conjunct is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list cc '?x) (list aa '?x)) 'CxWell {:direction :forward}))))
    (testing "and through the second, which is the one a single-predicate key would miss"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list cc '?x) (list bb '?x)) 'CxWell {:direction :forward}))))))

;; ---- backward agreement: a NAF antecedent under rule expansion ----------
;; A backward-only rule cannot be pre-materialized by forward chaining, so whoever
;; expands it has to evaluate the `unknown` itself.  Both backward chainers do, and this
;; is the analogue of the `different`-in-a-backward-rule case: the invariant is that no
;; two readers of one rule disagree about it, forward chaining included.

(tu/deftest-kb every-backward-chainer-evaluates-unknown-in-a-backward-only-rule
  (tu/with-terms [pp qq rr Aa Bb]
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x)))
                             (list 'rr '?x)))
              'CxWell)
    (v/assert kb (list 'pp Aa) 'CxWell)
    (v/assert kb (list 'pp Bb) 'CxWell)
    (v/assert kb (list 'qq Bb) 'CxWell)
    (testing "the rule forward-derives nothing (it is backward-only)"
      (is (empty? (v/sentexes-matching kb (list 'rr '?x) 'CxWell))))
    (testing "every backward chainer expands the rule and honours the unknown"
      ;; the node engine (`query` at a depth) and the recur DFS must agree
      (doseq [provable? [#(v/query? kb % 'CxWell {:max-depth 2})
                         #(v/provable? kb % 'CxWell)]]
        (is (provable? (list 'rr Aa)) "qq Aa absent -> provable")
        (is (not (provable? (list 'rr Bb))) "qq Bb present -> not provable"))
      (is (= 1 (count (v/prove kb (list 'rr Aa) 'CxWell))))
      (is (= 0 (count (v/prove kb (list 'rr Bb) 'CxWell)))))))

;; ---- prove/backward now evaluate a deferred antecedent ------------------
;; The gap that was: the recursive chainer discharged an antecedent by fact
;; matching + rule expansion only, so a rule with a DEFERRED antecedent (different /
;; evaluate / unknown) proved nothing there — while `ask` and forward chaining honoured
;; it.  A backward-ONLY rule forces the backward path (forward cannot pre-materialize).

(tu/deftest-kb prove-and-backward-honour-every-deferred-antecedent
  (tu/with-terms [rel distinctPair age nextAge Ann Bob Tom]
    ;; `different` — the unique-name test
    (v/assert kb (list rel Ann Bob) 'CxWell)
    (v/assert kb (list rel Ann Ann) 'CxWell)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list rel '?x '?y) (list 'different '?x '?y))
                             (list distinctPair '?x '?y)))
              'CxWell)
    (testing "different: prove and backward honour it in a backward-only rule"
      (is (v/provable? kb (list distinctPair Ann Bob) 'CxWell))
      (is (not (v/provable? kb (list distinctPair Ann Ann) 'CxWell)))
      (is (= 1 (count (v/prove kb (list distinctPair Ann Bob) 'CxWell))))
      (is (= 0 (count (v/prove kb (list distinctPair Ann Ann) 'CxWell)))))
    ;; `evaluate` — computed, binds its output
    (v/assert kb (list age Tom 40) 'CxWell)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list age '?p '?n) (list 'evaluate '?next (list '+ '?n 1)))
                             (list nextAge '?p '?next)))
              'CxWell)
    (testing "evaluate: prove checks and backward binds the computed value"
      (is (v/provable? kb (list nextAge Tom 41) 'CxWell))
      (is (not (v/provable? kb (list nextAge Tom 99) 'CxWell)))
      (is (= [41] (map #(get % '?a) (v/prove kb (list nextAge Tom '?a) 'CxWell)))))))

;; ---- belief-sensitivity: unknown reads belief, not mere storage ---------
;; `(unknown S)` holds of an `S` that is stored but currently OUT (a defeated
;; default), because a level-6 match is belief-filtered.  Closed-world negation is
;; about what is *believed*, not what happens to sit in the store.

(tu/deftest-kb unknown-holds-of-a-defeated-default
  (tu/with-terms [happy Zed]
    (v/assert kb (list 'happy Zed) 'CxWell {:strength :default})
    (testing "while believed, it is not unknown"
      (is (not (v/ask? kb (list 'unknown (list 'happy Zed))))))
    ;; a monotonic negation defeats the default: (happy Zed) goes OUT but stays stored
    (v/assert kb (list 'not (list 'happy Zed)) 'CxWell {:strength :monotonic})
    (testing "the default is now stored-but-disbelieved"
      (is (some? (v/handle-of kb (list 'happy Zed) 'CxWell)) "still stored")
      (is (not (v/ask? kb (list 'happy Zed) 'CxWell)) "but not believed"))
    (testing "so the belief-sensitive unknown now holds"
      (is (v/ask? kb (list 'unknown (list 'happy Zed))))
      (is (not (v/ask? kb (list 'unknown (list 'not (list 'happy Zed)))))
          "the believed negation is *not* unknown"))))

(tu/deftest-kb a-defeat-that-releases-an-unknown-antecedent-is-order-independent
  ;; `(pp ?x) & (unknown (happy ?x)) => (rr ?x)`, over a default `(happy Zed)` that a
  ;; monotonic `(not (happy Zed))` defeats.  With the defeat in place the NAF query holds
  ;; (`unknown-holds-of-a-defeated-default`), so the rule derives `(rr Zed)` in every
  ;; assertion order.  When the negation arrives last, the firing was refused while
  ;; `(happy Zed)` was believed, and the defeat that releases the query moves `(happy Zed)`
  ;; OUT without removing it from the store — so no re-check re-evaluates the firing.
  (tu/with-terms [pp happy rr Zed]
    (let [rule     (list 'implies (list 'and (list pp '?x) (list 'unknown (list happy '?x)))
                         (list rr '?x))
          assert-a (fn [s opts] (v/assert kb s 'CxWell opts))
          defeat   #(assert-a (list 'not (list happy Zed)) {:strength :monotonic})
          derive   #(do (assert-a rule {:direction :forward})
                        (assert-a (list pp Zed) {}))
          happy!   #(assert-a (list happy Zed) {:strength :default})]
      (testing "the defeat arrives before the rule fires: the conclusion is derived"
        (happy!) (defeat) (derive)
        (is (v/ask? kb (list 'unknown (list happy Zed)) 'CxWell))
        (is (v/ask? kb (list rr Zed) 'CxWell)))))
  (tu/with-terms [pp happy rr Zed]
    (let [rule     (list 'implies (list 'and (list pp '?x) (list 'unknown (list happy '?x)))
                         (list rr '?x))
          assert-a (fn [s opts] (v/assert kb s 'CxWell opts))]
      (assert-a rule {:direction :forward})
      (assert-a (list pp Zed) {})
      (assert-a (list happy Zed) {:strength :default})
      (testing "while the default is believed the firing is refused"
        (is (not (v/ask? kb (list rr Zed) 'CxWell))))
      (assert-a (list 'not (list happy Zed)) {:strength :monotonic})
      (testing "the defeat arrives after the refused firing: the NAF query now holds"
        (is (not (v/ask? kb (list happy Zed) 'CxWell)) "the default is defeated")
        (is (v/ask? kb (list 'unknown (list happy Zed)) 'CxWell)))
      (testing "so the rule reading the same query derives the conclusion, as in the other order"
        (let [derived? (v/ask? kb (list rr Zed) 'CxWell)]
          (is derived? "(rr Zed) is derived once the defeat releases (unknown (happy Zed))"))))))

;; ---- block-if-any across several unknown antecedents --------------------
;; Each `(unknown S)` is an INDEPENDENT block condition (unlike an exception's
;; conjuncts, which block only when all hold): any one derivable inner blocks.

(tu/deftest-kb multiple-unknowns-block-if-any-holds
  (tu/with-terms [pp qq ss rr Aa]
    (v/assert kb (list 'implies (list 'and (list 'pp '?x)
                                      (list 'unknown (list 'qq '?x))
                                      (list 'unknown (list 'ss '?x)))
                       (list 'rr '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list 'pp Aa) 'CxWell)
    (testing "fires only when BOTH inners are absent"
      (is (v/ask? kb (list 'rr Aa) 'CxWell)))
    (let [h (v/assert kb (list 'ss Aa) 'CxWell)]
      (testing "one inner holding is enough to block"
        (is (not (v/ask? kb (list 'rr Aa) 'CxWell))))
      (v/retract! kb h)
      (testing "and revives when it leaves"
        (is (v/ask? kb (list 'rr Aa) 'CxWell))))))

;; ---- subtype fan-out: the NAF query and its trigger follow genl ---------
;; `(unknown (super ?x))` must be blocked by a `(sub ?x)` fact — the level-6 query
;; fans the functor over its spec closure — and a *later* `sub` fact must trigger a
;; re-check of a rule that only ever mentions `super`.

(tu/deftest-kb unknown-follows-the-subtype-closure
  ;; bound (gensym'd) types/predicates throughout, so `genl`, the rule's NAF query,
  ;; and the subtype fact all name the *same* terms
  (tu/with-terms [sub super pp rr Aa]
    (v/assert kb (list 'genl sub super) 'CxWell)
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list super '?x)))
                       (list rr '?x))
              'CxWell {:direction :forward})
    (v/assert kb (list pp Aa) 'CxWell)
    (testing "with no super/sub membership, it fires"
      (is (v/ask? kb (list rr Aa) 'CxWell)))
    (let [h (v/assert kb (list sub Aa) 'CxWell)]
      (testing "a subtype fact satisfies the supertype NAF query and blocks it"
        (is (not (v/ask? kb (list rr Aa) 'CxWell))
            "(sub Aa) makes (super Aa) derivable, so (unknown (super Aa)) fails"))
      (v/retract! kb h)
      (testing "removing it revives the conclusion"
        (is (v/ask? kb (list rr Aa) 'CxWell))))))

;; ---- context scoping: a fact the conclusion cannot see does not block ---
;; The `unknown` is evaluated in the conclusion's PLACEMENT context, so a fact in a
;; sibling context — one the placement context does not see via genlCx — cannot
;; make its inner derivable.  This is why it is a derive-time check, not a global
;; `?ctx` join filter.

(tu/deftest-kb unknown-respects-the-placement-context
  (tu/with-terms [pp qq rr Aa CxPar CxSubA CxSubB]
    ;; two sibling contexts under a common parent; siblings do not see each other
    (v/assert kb (list 'genlCx CxSubA CxPar) 'CxWell)
    (v/assert kb (list 'genlCx CxSubB CxPar) 'CxWell)
    ;; rule + generator live in SubA, so the conclusion is placed in SubA
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x)))
                       (list 'rr '?x))
              CxSubA {:direction :forward})
    (v/assert kb (list 'pp Aa) CxSubA)
    (testing "the conclusion is derived in SubA"
      (is (v/ask? kb (list 'rr Aa) CxSubA)))
    ;; a qq fact in the *sibling* SubB is invisible from SubA, so it must NOT block
    (let [h (v/assert kb (list 'qq Aa) CxSubB)]
      (testing "a fact in an unseen sibling context does not satisfy the NAF query"
        (is (v/ask? kb (list 'rr Aa) CxSubA)
            "(qq Aa) in SubB is not visible from SubA, so (unknown (qq Aa)) still holds"))
      (v/retract! kb h))
    ;; but a qq fact in SubA itself IS visible, so it blocks
    (let [h (v/assert kb (list 'qq Aa) CxSubA)]
      (testing "a fact in the placement context does block"
        (is (not (v/ask? kb (list 'rr Aa) CxSubA))))
      (v/retract! kb h))))

;; ---- asked again at every reader below the placement --------------------
;; A reader below the placement context asks the question again against what it sees,
;; and reads the firing as withdrawn where the query holds (docs/naf.md, "Evaluated in
;; the placement context, not the join").  The placement keeps its firing.

(tu/deftest-kb an-unknown-is-asked-again-at-a-reader-below-the-placement
  ;; CxA: pp & unknown(qq) => rr, (pp Aa).  CxB sees CxA: (ss Aa) and rr & ss => tt.
  (tu/with-terms [pp qq rr ss tt Aa CxA CxB]
    (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                       (list rr '?x))
              CxA {:direction :forward})
    (v/assert kb (list 'implies (list 'and (list rr '?x) (list ss '?x)) (list tt '?x))
              CxB {:direction :forward})
    (v/assert kb (list pp Aa) CxA)
    (v/assert kb (list ss Aa) CxB)
    (let [rr-h  (v/handle-of kb (list rr Aa) CxA)
          tt-h  (v/handle-of kb (list tt Aa) CxB)
          reads (fn [] [(v/believed? kb rr-h CxA) (v/believed? kb rr-h CxB)
                        (v/ask? kb (list rr Aa) CxB) (v/believed? kb tt-h CxB)])]
      (is (= [true true true true] (reads)))
      (let [h (v/assert kb (list qq Aa) CxB)]
        (is (= [true false false false] (reads))
            "CxB reads (qq Aa), so the firing and what rests on it are withdrawn there")
        (v/retract! kb h))
      (is (= [true true true true] (reads))))))

(tu/deftest-kb an-exceptWhen-is-asked-again-at-a-reader-below-the-placement
  (tu/with-terms [bird penguin flies Opus CxA CxB]
    (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x))))
              CxA)
    (v/assert kb (list bird Opus) CxA)
    (v/assert kb (list penguin Opus) CxB)
    (let [h (v/handle-of kb (list flies Opus) CxA)]
      (is (= [true false] [(v/believed? kb h CxA) (v/believed? kb h CxB)])))))

(tu/deftest-kb a-blocker-seen-through-a-second-parent-withdraws-the-firing-below-both
  ;; CxJ sees CxA, which places the firing, and CxC, which holds the blocker
  (tu/with-terms [pp qq rr Aa CxA CxC CxJ]
    (doseq [[lo hi] [[CxJ CxA] [CxJ CxC]]]
      (v/assert kb (list 'genlCx lo hi) 'CxUniverse {:strength :monotonic}))
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                       (list rr '?x))
              CxA {:direction :forward})
    (v/assert kb (list pp Aa) CxA)
    (v/assert kb (list qq Aa) CxC)
    (let [h (v/handle-of kb (list rr Aa) CxA)]
      (is (= [true false] [(v/believed? kb h CxA) (v/believed? kb h CxJ)])))))

(tu/deftest-kb an-except-and-an-unknown-withdraw-one-firing-at-one-reader-independently
  (tu/with-terms [pp qq rr Aa CxA CxB]
    (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                       (list rr '?x))
              CxA {:direction :forward})
    (v/assert kb (list pp Aa) CxA)
    (let [h   (v/handle-of kb (list rr Aa) CxA)
          blk (v/assert kb (list qq Aa) CxB)
          ex  (v/assert kb (list 'except (sx/sentex-handle h)) CxB)
          at  (fn [] [(v/believed? kb h CxA) (v/believed? kb h CxB)])]
      (is (= [true false] (at)))
      (v/retract! kb blk)
      (is (= [true false] (at)) "the except alone still hides it at CxB")
      (let [blk (v/assert kb (list qq Aa) CxB)]
        (v/retract! kb ex)
        (is (= [true false] (at)) "the blocker alone still withdraws it at CxB")
        (v/retract! kb blk))
      (is (= [true true] (at))))))

;; ---- a guard below the placement places a defeat ------------------------
;; CxB sees CxA.  CxA holds (pp Zed) and the guarded rule G, which fires (rr Zed) = F at
;; CxA; (qq Zed) in CxB blocks G there.  G guards with `exceptWhen` or with `unknown`.
;; H, (pp ?x) & (tt ?x) => (rr ?x) over (tt Zed) in CxA, is a second justification of F
;; that no guard blocks.

(defn- guard-rule
  "Rule G of the lattice above, guarded by `kind`."
  [kind pp qq rr]
  (case kind
    :except  (list 'exceptWhen (list qq '?x)
                   (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x))))
    :unknown (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x))) (list rr '?x))))

(defn- guard-reading
  "Build the lattice above in `kb` with the steps `ops` in order (`:pp`, `:qq`, `:g`, `:h`,
  `:uu`, `:g2`, `:premise`, `:retract-qq`), read `[CxA believes F, CxB believes F, the
  defeats of F stored at CxA, and at CxB]`, and retract what it asserted."
  [kb kind ops]
  (tu/with-terms [pp qq rr tt uu Zed CxA CxB]
    (let [as  (fn [s c] (v/assert kb s c (if (= 'implies (first s)) {:direction :forward} {})))
          hs  (volatile! [(v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
                          (as (list tt Zed) CxA)])
          qqh (volatile! nil)]
      (doseq [op ops]
        (let [h (case op
                  :pp      (as (list pp Zed) CxA)
                  :qq      (vreset! qqh (as (list qq Zed) CxB))
                  :g       (as (guard-rule kind pp qq rr) CxA)
                  :h       (as (list 'implies (list 'and (list pp '?x) (list tt '?x)) (list rr '?x)) CxA)
                  :g2      (as (list 'implies (list 'and (list pp '?x) (list 'unknown (list uu '?x)))
                                     (list rr '?x))
                               CxA)
                  :uu      (as (list uu Zed) CxB)
                  :premise (as (list rr Zed) CxA)
                  :retract-qq (do (v/retract! kb @qqh) nil))]
          (when h (vswap! hs conj h))))
      (let [f       (v/handle-of kb (list rr Zed) CxA)
            defeats (fn [c] (count (filter #(= (list 'defeat (list 'sentexHandle f)) (:sentence %))
                                           (v/sentexes-matching kb (list 'defeat '?h) c))))
            r       [(v/believed? kb f CxA) (v/believed? kb f CxB) (defeats CxA) (defeats CxB)]]
        (doseq [h (rseq @hs)] (when (v/sentex kb h) (v/retract! kb h)))
        r))))

(tu/deftest-kb a-guard-below-the-placement-places-a-defeat-and-a-second-justification-keeps-f
  (doseq [kind [:except :unknown]]
    (testing kind
      (is (= #{[true false 0 1]}
             (into #{} (map #(guard-reading kb kind %)) (oi/permutations [:pp :qq :g])))
          "without H, CxB does not believe F, and the defeat is stored at CxB alone")
      (is (= #{[true true 0 1]}
             (into #{} (map #(guard-reading kb kind %)) (oi/permutations [:pp :qq :g :h])))
          "H's justification is not covered at CxB"))))

(tu/deftest-kb a-second-guarded-justification-keeps-f-until-its-guard-holds-too
  (doseq [kind [:except :unknown]]
    (testing kind
      (is (= [true true 0 1] (guard-reading kb kind [:pp :qq :g :g2])))
      (is (= [true false 0 1] (guard-reading kb kind [:pp :qq :g :g2 :uu])))
      (is (= [true true 0 1] (guard-reading kb kind [:pp :qq :g :premise]))
          "a premise is a justification no guard defeat covers"))))

(tu/deftest-kb retracting-the-blocker-takes-the-guard-defeat-out
  (doseq [kind [:except :unknown]]
    (testing kind
      (is (= [true true 0 0] (guard-reading kb kind [:pp :qq :g :retract-qq])))
      (is (= [true true 0 0] (guard-reading kb kind [:pp :qq :g :h :retract-qq]))))))

;; ---- a guard met through a genl edge ---------------------------------------
;; G's guard (mammal_t ?x) is met by (dog_t Zed) over (genl dog_t mammal_t).  The guard
;; defeat of F = (rr Zed) rests on that edge as it rests on the blocker.

(defn- climbed-guard-rule
  "Rule G guarded by `kind` on the type `mammal_t`."
  [kind pp rr mammal_t]
  (case kind
    :except  (list 'exceptWhen (list mammal_t '?x)
                   (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x))))
    :unknown (list 'implies (list 'and (list pp '?x) (list 'unknown (list mammal_t '?x)))
                   (list rr '?x))))

(defn- guard-defeats-at
  "The stored `(defeat (sentexHandle f))` sentexes whose own context is `c`."
  [kb f c]
  (filterv #(and (= c (:context %)) (= (list 'defeat (sx/sentex-handle f)) (:sentence %)))
           (v/sentexes-with-functor kb 'defeat)))

(defn- edge-below-reading
  "CxB sees CxA.  CxA holds (dog_t Zed), (pp Zed) and G; CxB holds (genl dog_t mammal_t).
  Assert the steps `ops` in order, read [CxA believes F, CxB believes F, the defeats of F
  stored at CxB, whether the edge is an antecedent of one of them], and retract."
  [kb kind ops]
  (tu/with-terms [pp rr dog_t mammal_t Zed CxA CxB]
    (let [as   (fn [s c] (v/assert kb s c (if (= 'implies (first s)) {:direction :forward} {})))
          hs   (volatile! [(v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
                           (as (list 'genl mammal_t 'thing) 'CxUniverse)])
          edge (volatile! nil)]
      (doseq [op ops]
        (vswap! hs conj (case op
                          :dog  (as (list dog_t Zed) CxA)
                          :pp   (as (list pp Zed) CxA)
                          :g    (as (climbed-guard-rule kind pp rr mammal_t) CxA)
                          :edge (vreset! edge (as (list 'genl dog_t mammal_t) CxB)))))
      (let [f  (v/handle-of kb (list rr Zed) CxA)
            ds (guard-defeats-at kb f CxB)
            r  [(v/believed? kb f CxA) (v/believed? kb f CxB) (count ds)
                (boolean (some #(some #{@edge} (:antecedents %))
                               (mapcat #(v/supporting-justifications kb (:id %)) ds)))]]
        (doseq [h (rseq @hs)] (when (v/sentex kb h) (v/retract! kb h)))
        r))))

(tu/deftest-kb a-guard-met-through-a-genl-edge-below-the-placement-places-a-defeat-resting-on-the-edge
  (doseq [kind [:except :unknown]]
    (testing kind
      (is (= #{[true false 1 true]}
             (into #{} (map #(edge-below-reading kb kind %)) (oi/permutations [:dog :pp :g :edge])))
          "CxA does not see the edge and believes F; CxB sees it and does not"))))

(defn- edge-hidden-reading
  "CxC sees CxB, which sees CxA.  CxA holds (pp Zed), G and (genl dog_t mammal_t); CxB
  holds (dog_t Zed); CxC hides the edge by `hide`: `:except`, an except of it, or
  `:denial`, `(not (genl dog_t mammal_t))` at `:monotonic`, whose placed defeat hides the
  edge there.  Read [F at CxA, at CxB, at CxC, (mammal_t Zed) asked at CxC], and
  retract."
  [kb kind hide]
  (tu/with-terms [pp rr dog_t mammal_t Zed CxA CxB CxC]
    (let [as   (fn [s c] (v/assert kb s c (if (= 'implies (first s)) {:direction :forward} {})))
          hs   (volatile! [(v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
                           (v/assert kb (list 'genlCx CxC CxB) 'CxUniverse {:strength :monotonic})
                           (as (list 'genl mammal_t 'thing) 'CxUniverse)])
          edge (as (list 'genl dog_t mammal_t) CxA)]
      (vswap! hs into [edge
                       (as (list pp Zed) CxA)
                       (as (climbed-guard-rule kind pp rr mammal_t) CxA)
                       (as (list dog_t Zed) CxB)])
      (vswap! hs conj (case hide
                        :except (as (list 'except (sx/sentex-handle edge)) CxC)
                        :denial (v/assert kb (list 'not (list 'genl dog_t mammal_t)) CxC
                                          {:strength :monotonic})))
      (let [f (v/handle-of kb (list rr Zed) CxA)
            r [(v/believed? kb f CxA) (v/believed? kb f CxB) (v/believed? kb f CxC)
               (v/ask? kb (list mammal_t Zed) CxC)]]
        (doseq [h (rseq @hs)] (when (v/sentex kb h) (v/retract! kb h)))
        r))))

(tu/deftest-kb a-guard-met-by-a-genl-closure-pair-places-a-defeat-resting-on-the-path
  ;; G's guard (genl ?k mammal_t) holds of dog_t over (genl dog_t canine_t) in CxA and
  ;; (genl canine_t mammal_t) in CxB below: no stored edge states the pair, the closure does
  (doseq [kind [:except :unknown]]
    (testing kind
      (tu/with-terms [pp rr dog_t canine_t mammal_t Zed CxA CxB]
        (let [as  (fn [s c] (v/assert kb s c (if (= 'implies (first s)) {:direction :forward} {})))
              g   (case kind
                    :except  (list 'exceptWhen (list 'genl '?k mammal_t)
                                   (list 'set/forwardRule (list 'implies (list pp '?x '?k) (list rr '?x))))
                    :unknown (list 'implies (list 'and (list pp '?x '?k) (list 'unknown (list 'genl '?k mammal_t)))
                                   (list rr '?x)))
              hs  [(v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
                   (as (list 'genl mammal_t 'thing) 'CxUniverse)
                   (as (list 'genl canine_t 'thing) 'CxUniverse)
                   (as (list pp Zed dog_t) CxA)
                   (as g CxA)]
              e1  (as (list 'genl dog_t canine_t) CxA)
              e2  (as (list 'genl canine_t mammal_t) CxB)
              f   (v/handle-of kb (list rr Zed) CxA)
              ds  (guard-defeats-at kb f CxB)
              as' (into #{} (comp (mapcat #(v/supporting-justifications kb (:id %))) (mapcat :antecedents)) ds)]
          (is (= [true false 1 true]
                 [(v/believed? kb f CxA) (v/believed? kb f CxB) (count ds) (every? as' [e1 e2])]))
          (v/retract! kb e2)
          (is (= [true true] [(v/believed? kb f CxA) (v/believed? kb f CxB)])
              "the defeat rests on the lower edge, so retracting it takes the defeat OUT")
          (doseq [h (concat [e1] (rseq hs))] (when (v/sentex kb h) (v/retract! kb h))))))))

(tu/deftest-kb hiding-the-genl-edge-a-guard-climbed-below-its-defeat-gives-the-firing-back-there
  (doseq [kind [:except :unknown]
          hide [:except :denial]]
    (testing [kind hide]
      (is (= [true false true false] (edge-hidden-reading kb kind hide))
          "the guard holds at CxB and not at CxC, which does not see dog_t under mammal_t"))))

;; ---- a blocker an except hides and a meta-except restores below --------------

(defn- restored-blocker-reading
  "CxB sees CxA.  CxA holds (pp Zed), G (guarded by `kind` on (qq ?x)), (qq Zed), and X =
  (except (qq Zed)); CxB holds M = (except X).  Assert the steps `ops` in order, read [F at
  CxA, F at CxB, the defeats of F stored at CxB, (qq Zed) asked at CxA, at CxB], and
  retract."
  [kb kind ops]
  (tu/with-terms [pp qq rr Zed CxA CxB]
    (let [as (fn [s c] (v/assert kb s c (if (= 'implies (first s)) {:direction :forward} {})))
          hs (volatile! [(v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})])
          at (volatile! {})]
      (doseq [op ops]
        (let [h (case op
                  :pp (as (list pp Zed) CxA)
                  :g  (as (guard-rule kind pp qq rr) CxA)
                  :qq (as (list qq Zed) CxA)
                  :x  (as (list 'except (sx/sentex-handle (:qq @at))) CxA)
                  :m  (as (list 'except (sx/sentex-handle (:x @at))) CxB))]
          (vswap! at assoc op h)
          (vswap! hs conj h)))
      (let [f (v/handle-of kb (list rr Zed) CxA)
            r [(v/believed? kb f CxA) (v/believed? kb f CxB) (count (guard-defeats-at kb f CxB))
               (v/ask? kb (list qq Zed) CxA) (v/ask? kb (list qq Zed) CxB)]]
        (doseq [h (rseq @hs)] (when (v/sentex kb h) (v/retract! kb h)))
        r))))

(defn- meta-orders
  "The orders of `[:pp :g :qq :x :m]` that state the blocker before its except and the
  except before the meta-except."
  []
  (filter (fn [o] (let [i #(.indexOf ^java.util.List (vec o) %)]
                    (< (i :qq) (i :x) (i :m))))
          (oi/permutations [:pp :g :qq :x :m])))

(tu/deftest-kb a-blocker-a-meta-except-restores-below-the-placement-places-a-guard-defeat-there
  (doseq [kind [:except :unknown]]
    (testing kind
      (is (= #{[true false 1 false true]}
             (into #{} (map #(restored-blocker-reading kb kind %)) (meta-orders)))
          "CxA reads the blocker hidden and believes F; CxB reads it restored and does not"))))

(tu/deftest-kb a-blocker-hidden-at-the-join-and-restored-below-it-places-a-guard-defeat-below
  ;; CxJ sees CxA (pp Zed, G) and CxQ ((qq Zed) and its except X); CxB sees CxJ and holds
  ;; M = (except X).  `exception-aware-placements` places a firing over these handles at
  ;; CxB; the guard defeat owes the same placement
  (doseq [kind [:except :unknown]]
    (testing kind
      (tu/with-terms [pp qq rr Zed CxA CxQ CxJ CxB]
        (let [as (fn [s c] (v/assert kb s c (if (= 'implies (first s)) {:direction :forward} {})))
              es (mapv (fn [[lo hi]] (v/assert kb (list 'genlCx lo hi) 'CxUniverse {:strength :monotonic}))
                       [[CxJ CxA] [CxJ CxQ] [CxB CxJ]])
              p  (as (list pp Zed) CxA)
              g  (as (guard-rule kind pp qq rr) CxA)
              q  (as (list qq Zed) CxQ)
              x  (as (list 'except (sx/sentex-handle q)) CxQ)
              m  (as (list 'except (sx/sentex-handle x)) CxB)
              f  (v/handle-of kb (list rr Zed) CxA)]
          (is (= [true true false] [(v/believed? kb f CxA) (v/believed? kb f CxJ) (v/believed? kb f CxB)]))
          (is (= 1 (count (guard-defeats-at kb f CxB))))
          (v/retract! kb m)
          (is (= [true true true] [(v/believed? kb f CxA) (v/believed? kb f CxJ) (v/believed? kb f CxB)])
              "the meta-except leaving hides the blocker at CxB again")
          (doseq [h (concat [x q g p] (rseq es))] (when (v/sentex kb h) (v/retract! kb h))))))))

(tu/deftest-kb a-guard-defeat-beside-a-released-nogood-covers-only-its-firing
  ;;   CxUniverse  (disjoint dog cat)
  ;;     ├─ CxA    (pp Zed) (tt Zed), G: (pp ?x) exceptWhen (qq ?x) ⇒ (cat ?x),
  ;;     │         H: (pp ?x) & (tt ?x) ⇒ (cat ?x)          F = (cat Zed), placed in CxA
  ;;     └─ CxB    (dog Zed) monotonic, (qq Zed)
  ;;   CxD sees CxA and CxB: the nogood {F (dog Zed)} and G's guard each place
  ;;       (defeat F) there, one handle with a justification each
  ;;     └─ CxR sees CxD   (except (disjoint dog cat))
  ;;
  ;; At CxR the nogood is released, and the guard covers G's justification alone, so F
  ;; is believed there through H's.
  (tu/with-terms [pp qq tt cat dog Zed CxA CxB CxD CxR]
    (doseq [t [cat dog]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [[lo hi] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxD CxA] [CxD CxB] [CxR CxD]]]
      (v/assert kb (list 'genlCx lo hi) 'CxUniverse {:strength :monotonic}))
    (let [dj (v/assert kb (list 'disjoint dog cat) 'CxUniverse)]
      (v/assert kb (guard-rule :except pp qq cat) CxA)
      (v/assert kb (list 'implies (list 'and (list pp '?x) (list tt '?x)) (list cat '?x)) CxA
                {:direction :forward})
      (v/assert kb (list pp Zed) CxA)
      (v/assert kb (list tt Zed) CxA)
      (v/assert kb (list dog Zed) CxB {:strength :monotonic})
      (v/assert kb (list qq Zed) CxB)
      (v/assert kb (list 'except (list 'sentexHandle dj)) CxR)
      (let [f (v/handle-of kb (list cat Zed) CxA)
            d (v/handle-of kb (list 'defeat (list 'sentexHandle f)) CxD)]
        (is (= 2 (count (:support (v/why kb d)))))
        (is (= [true false true] (mapv #(v/believed? kb f %) [CxA CxD CxR])))))))

;; ---- a guard a prover answers below the placement ---------------------------

(defn- transitive-guard-reading
  "CxB sees CxA.  CxA holds (transitive ancestorOf), (pp Bob), (ancestorOf Bob Al) and G,
  guarded by `kind` on (ancestorOf ?x Zed); CxB holds (ancestorOf Al Zed), so the guard
  holds at CxB through the transitive closure and no stored sentex states it.  Assert the
  steps `ops` in order, read [F at CxA, F at CxB, the defeats of F stored at CxB, whether
  one rests on both hops], and retract."
  [kb kind ops]
  (tu/with-terms [pp rr ancestorOf Bob Al Zed CxA CxB]
    (let [as   (fn [s c] (v/assert kb s c (if (= 'implies (first s)) {:direction :forward} {})))
          hs   (volatile! [(v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
                           (as (list 'transitive ancestorOf) CxA)])
          hops (volatile! [])
          hop  (fn [s c] (let [h (as s c)] (vswap! hops conj h) h))]
      (doseq [op ops]
        (vswap! hs conj (case op
                          :pp   (as (list pp Bob) CxA)
                          :g    (as (case kind
                                      :except  (list 'exceptWhen (list ancestorOf '?x Zed)
                                                     (list 'set/forwardRule
                                                           (list 'implies (list pp '?x) (list rr '?x))))
                                      :unknown (list 'implies
                                                     (list 'and (list pp '?x)
                                                           (list 'unknown (list ancestorOf '?x Zed)))
                                                     (list rr '?x)))
                                    CxA)
                          :hop1 (hop (list ancestorOf Bob Al) CxA)
                          :hop2 (hop (list ancestorOf Al Zed) CxB))))
      (let [f  (v/handle-of kb (list rr Bob) CxA)
            ds (guard-defeats-at kb f CxB)
            r  [(v/believed? kb f CxA) (v/believed? kb f CxB) (count ds)
                (boolean (some #(every? (set (:antecedents %)) @hops)
                               (mapcat #(v/supporting-justifications kb (:id %)) ds)))]]
        (doseq [h (rseq @hs)] (when (v/sentex kb h) (v/retract! kb h)))
        r))))

(tu/deftest-kb a-guard-a-transitive-closure-meets-below-the-placement-places-a-defeat-resting-on-the-hops
  (doseq [kind [:except :unknown]]
    (testing kind
      (is (= #{[true false 1 true]}
             (into #{} (map #(transitive-guard-reading kb kind %))
                   (oi/permutations [:pp :g :hop1 :hop2])))
          "CxA does not reach Zed from Bob and believes F; CxB does and does not"))))

(defn- nested-guard-reading
  "CxB and CxC see CxA.  CxA holds (pp Zed) and G, guarded by `kind` on (and (qq ?x)
  (unknown (ss ?x))); CxB holds (qq Zed); CxC holds (ss Zed) when `ss?`, stated first or
  last by `ss-at`.  Read [F at CxA, F at CxB, the defeats of F stored at CxB], and
  retract."
  [kb kind ss? ss-at]
  (tu/with-terms [pp qq rr ss Zed CxA CxB CxC]
    (let [as   (fn [s c] (v/assert kb s c (if (= 'implies (first s)) {:direction :forward} {})))
          cnd  (list 'and (list qq '?x) (list 'unknown (list ss '?x)))
          g    (case kind
                 :except  (list 'exceptWhen cnd
                                (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x))))
                 :unknown (list 'implies (list 'and (list pp '?x) (list 'unknown cnd)) (list rr '?x)))
          ss!  #(when ss? [(as (list ss Zed) CxC)])
          hs   (-> [(v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
                    (v/assert kb (list 'genlCx CxC CxA) 'CxUniverse {:strength :monotonic})]
                   (into (when (= :first ss-at) (ss!)))
                   (into [(as (list pp Zed) CxA) (as g CxA) (as (list qq Zed) CxB)])
                   (into (when (= :last ss-at) (ss!))))
          f    (v/handle-of kb (list rr Zed) CxA)
          r    [(v/believed? kb f CxA) (v/believed? kb f CxB) (count (guard-defeats-at kb f CxB))]]
      (doseq [h (rseq hs)] (when (v/sentex kb h) (v/retract! kb h)))
      r)))

(tu/deftest-kb a-guard-with-an-inner-unknown-is-decided-at-the-placed-context-not-in-a-sibling
  (doseq [kind [:except :unknown]]
    (testing kind
      (is (= #{[true false 1]}
             (into #{} (for [ss? [false true] ss-at [:first :last]]
                         (nested-guard-reading kb kind ss? ss-at))))
          "CxB does not see (ss Zed) in CxC, so the guard holds at CxB whatever CxC holds"))))

;; ---- thereExists with a vector of quantified variables ------------------

(tu/deftest-kb there-exists-binds-a-vector-of-variables
  (tu/with-terms [rel Aa Bb]
    (v/assert kb (list 'rel Aa Bb) 'CxWell)
    (testing "a vector binder closes off all its variables"
      (is (= #{} (sx/free-vars (list 'thereExists ['?x '?y] (list 'rel '?x '?y)))))
      (is (v/ask? kb (list 'thereExists ['?x '?y] (list 'rel '?x '?y))))
      (is (not (v/ask? kb (list 'thereExists ['?x '?y] (list 'rel '?x 'NoSuchThing))))))))

(tu/deftest-kb a-lookup-budget-keeps-unknown-rather-than-inverting-it
  ;; dropping `UnknownProver` past the cap would not under-report: an empty result for
  ;; `(unknown S)` reads as "S is derivable" (docs/anytime.md)
  (tu/with-terms [flies Tweety]
    (let [g (list 'unknown (list flies Tweety))]
      (is (v/ask? kb g 'CxWell) "S is not derivable, so (unknown S) holds")
      (let [r (v/ask-within kb g 'CxWell {:max-cost :lookup})]
        (is (seq (:results r)) "the lookup budget keeps UnknownProver, not an inverted empty")
        (is (= :complete (:status r)))))))
