;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-test
  "Non-atomic terms (NATs) — docs/nat.md.

  A ground reifiable NAT `(FruitFn AppleTree)` reifies to an opaque `nat/` constant
  before it reaches the index (Strategy A), so it autoindexes like an atomic symbol;
  an unreifiable structural NAT `(QuantityFn 5 Kilogram)` stays structural.  The constant↔
  expression map is an ordinary `(termOfUnit K E)` fact, so rename rides the equality
  migration and remove rides the retraction sweep."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(defn- k-of
  "The reified constant a stored NAT-bearing sentence's arg1 became."
  [kb h] (second (:sentence (v/sentex kb h))))

;; ---- 1. round-trip -------------------------------------------------------

(tu/deftest-kb round-trip-stores-an-opaque-constant
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiableFunction FruitFn) 'UniverseContext)
    (v/assert kb (list 'resultIsa FruitFn fruit) 'UniverseContext)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'UniverseContext)
          k (k-of kb h)]
      (testing "the stored sentence holds an opaque constant, not the compound"
        (is (nat/reified-nat-symbol? k))
        (is (= (list 'color k 'Red) (:sentence (v/sentex kb h))))
        (is (not-any? sequential? (rest (:sentence (v/sentex kb h))))))
      (testing "the materialized result type holds"
        (is (seq (v/sentexes-matching kb (list fruit k) '?ctx))))
      (testing "a NAT-bearing query resolves to the stored constant"
        (is (= [{'?c 'Red}] (v/ask kb (list 'color (list FruitFn AppleTree) '?c) '?ctx))))
      (testing "display expands the constant back to its functional expression"
        (is (= (list 'color (list FruitFn AppleTree) 'Red)
               (nat/expand-expression kb (:sentence (v/sentex kb h))))))
      (testing "an unknown NAT resolves to no-match and mints nothing"
        (let [before (count (v/sentexes-matching kb (list 'termOfUnit '?k '?e) 'UniverseContext))]
          (is (empty? (v/sentexes-matching kb (list 'color (list FruitFn 'PearTree) '?c) '?ctx)))
          (is (= before (count (v/sentexes-matching kb (list 'termOfUnit '?k '?e) 'UniverseContext)))))))))

;; ---- 2. dedup ------------------------------------------------------------

(tu/deftest-kb the-same-nat-yields-the-same-constant
  (tu/with-terms [FruitFn AppleTree]
    (v/assert kb (list 'reifiableFunction FruitFn) 'UniverseContext)
    (let [h1 (v/assert kb (list 'color (list FruitFn AppleTree) 'Red)   'UniverseContext)
          h2 (v/assert kb (list 'taste (list FruitFn AppleTree) 'Sweet) 'UniverseContext)]
      (is (= (k-of kb h1) (k-of kb h2)))
      (testing "one termOfUnit maps the expression"
        (is (= 1 (count (v/sentexes-matching kb (list 'termOfUnit '?k (list FruitFn AppleTree))
                                             'UniverseContext))))))))

;; ---- 3. nested -----------------------------------------------------------

(tu/deftest-kb a-nested-nat-reifies-inner-then-outer
  (tu/with-terms [FruitFn BestTreeIn Orchard1]
    (v/assert kb (list 'reifiableFunction FruitFn) 'UniverseContext)
    (v/assert kb (list 'reifiableFunction BestTreeIn) 'UniverseContext)
    (let [h        (v/assert kb (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
                             'UniverseContext)
          inner-k  (nat/dedup-constant kb (list BestTreeIn Orchard1))
          outer-k  (k-of kb h)]
      (testing "both the inner and outer NAT have a termOfUnit"
        (is (nat/reified-nat-symbol? inner-k))
        (is (nat/reified-nat-symbol? outer-k))
        (is (= (list FruitFn inner-k) (nat/nat-expression kb outer-k)))
        (is (= (list BestTreeIn Orchard1) (nat/nat-expression kb inner-k))))
      (testing "display expands both levels"
        (is (= (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
               (nat/expand-expression kb (:sentence (v/sentex kb h)))))))))

;; ---- 4. rename -----------------------------------------------------------

(tu/deftest-kb rename-rewrites-the-expression-keeping-the-constant-stable
  (tu/with-terms [FruitFn AppleTree MalusTree]
    (v/assert kb (list 'reifiableFunction FruitFn) 'UniverseContext)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'UniverseContext)
          k (k-of kb h)]
      (v/assert kb (list 'rewriteOf MalusTree AppleTree) 'UniverseContext)   ; rename AppleTree -> MalusTree
      (testing "the constant is stable and its expression is rewritten"
        (is (= (list FruitFn MalusTree) (nat/nat-expression kb k)))
        (is (= k (nat/dedup-constant kb (list FruitFn MalusTree))))
        (is (= 1 (count (v/sentexes-matching kb (list 'termOfUnit '?k (list FruitFn MalusTree))
                                             'UniverseContext)))))
      (testing "the retired spelling stays a usable question, resolving to the same K"
        ;; AppleTree is deprecated to MalusTree, so a goal naming the old term rewrites
        ;; to the new expression before lookup (docs/equality.md) and still finds K
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))))))

(tu/deftest-kb rename-collision-merges-the-two-constants
  (tu/with-terms [FruitFn AppleTree MalusTree]
    (v/assert kb (list 'reifiableFunction FruitFn) 'UniverseContext)
    (let [ha (v/assert kb (list 'color (list FruitFn AppleTree) 'Red)   'UniverseContext)
          hm (v/assert kb (list 'taste (list FruitFn MalusTree) 'Sweet) 'UniverseContext)]
      (is (not= (k-of kb ha) (k-of kb hm)))
      (v/assert kb (list 'rewriteOf MalusTree AppleTree) 'UniverseContext)
      (testing "the colliding constants merge to one"
        (is (empty? (nat/colliding-constant-groups kb)))
        (is (= 1 (count (v/sentexes-matching kb (list 'termOfUnit '?k (list FruitFn MalusTree))
                                             'UniverseContext))))
        (is (some? (nat/dedup-constant kb (list FruitFn MalusTree))))))))

;; ---- 5. remove -----------------------------------------------------------

(tu/deftest-kb removing-the-last-use-collects-the-orphaned-reified-nat
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiableFunction FruitFn) 'UniverseContext)
    (v/assert kb (list 'resultIsa FruitFn fruit) 'UniverseContext)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'UniverseContext)
          k (k-of kb h)]
      (is (some? (nat/nat-expression kb k)))
      (v/retract! kb h)
      (testing "the reified NAT constant and its bookkeeping are gone, no dangling nat/ symbol"
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb)))))))

;; ---- 6. unreifiable gate -------------------------------------------------

(tu/deftest-kb an-unreifiable-nat-stays-structural
  (tu/with-terms [QuantityFn Obj]
    (v/assert kb (list 'unreifiableFunction QuantityFn) 'UniverseContext)
    (let [nut (list QuantityFn 5 'Kilogram)
          h   (v/assert kb (list 'mass Obj nut) 'UniverseContext)]
      (testing "the compound is stored structurally, not minted"
        (is (= (list 'mass Obj nut) (:sentence (v/sentex kb h))))
        (is (nil? (nat/dedup-constant kb nut))))
      (testing "it round-trips unchanged"
        (is (seq (v/sentexes-matching kb (list 'mass Obj nut) '?ctx)))))))

;; ---- 7. no-op cost -------------------------------------------------------

(tu/deftest-kb with-no-reifiable-function-the-reify-pass-is-a-no-op
  (tu/with-terms [FruitFn AppleTree]
    (testing "the gate is off and a plain compound is stored verbatim"
      (is (false? (nat/any-reifiable-functions? kb)))
      ;; a compound argument with no reifiableFunction declared is left structural
      (let [h (v/assert kb (list 'grows (list FruitFn AppleTree) 'Spring) 'UniverseContext)]
        (is (= (list 'grows (list FruitFn AppleTree) 'Spring) (:sentence (v/sentex kb h))))))))

;; ---- 8. every read path asks the same question ---------------------------
;;
;; A NAT reifies on the *write* path, so every read path has to reify its goal to meet
;; the stored constant.  `core/prepare-goal-for-read` is that step, and the interesting
;; failure is not a wrong answer but a **silently empty** one: a path that skips it
;; matches the compound against a store that holds a symbol and finds nothing, which
;; reads exactly like a KB that was never told.  So the claim is parity, checked path
;; by path rather than inferred from the one that works.

(tu/deftest-kb every-read-path-reifies-the-nat-in-its-goal
  (tu/with-terms [CapitalOfFn France isCapital Yes]
    (v/assert kb (list 'reifiableFunction CapitalOfFn) 'UniverseContext)
    (let [h (v/assert kb (list isCapital (list CapitalOfFn France) Yes) 'UniverseContext)]
      (testing "the store holds a constant, so a goal spelled as the NAT must be reified"
        (is (nat/reified-nat-symbol? (second (:sentence (v/sentex kb h)))))))
    (doseq [goal [(list isCapital (list CapitalOfFn France) Yes)
                  (list isCapital (list CapitalOfFn France) '?w)]]
      (testing (str "the ground and open forms of " (pr-str goal))
        (is (= 1 (count (v/ask kb goal 'UniverseContext))))
        (is (= 1 (count (v/sentexes-matching kb goal 'UniverseContext))))
        (is (= 1 (count (v/prove kb [goal] 'UniverseContext))))
        (testing "the anytime ask is the same ask, not a differently-prepared one"
          (let [r (v/ask-within kb goal 'UniverseContext {})]
            (is (= :complete (:status r)))
            (is (= (v/ask kb goal 'UniverseContext) (:results r)))))
        (testing "and so are the two levels that claim to be the engine's dispatch"
          (is (= 1 (count (v/lookup kb 6 goal 'UniverseContext))))
          (is (= 1 (count (v/lookup kb 7 goal 'UniverseContext)))))))))

(tu/deftest-kb an-exceptWhen-query-meets-the-constant-its-fact-was-stored-under
  ;; The write walk descends a rule's antecedents, so an `(unknown <NAT goal>)` reifies
  ;; along with the rule around it.  An `exceptWhen`'s conjuncts arrive as a **vector**,
  ;; which is a list of forms rather than a literal — and there the empty answer is not
  ;; merely a missing result.  An exception that cannot be answered does not hold
  ;; (docs/exceptions.md, the open-world reading), so the rule fires unguarded and
  ;; nothing says so.  One evaluator, so all three chainers or none.
  (tu/with-terms [CapitalOfFn France isCapital Yes bird flies Tweety]
    (v/assert kb (list 'reifiableFunction CapitalOfFn) 'UniverseContext)
    (v/assert kb (list bird Tweety) 'UniverseContext)
    (v/assert kb (list isCapital (list CapitalOfFn France) Yes) 'UniverseContext)
    (v/assert kb (list 'exceptWhen [(list isCapital (list CapitalOfFn France) Yes)]
                       (list 'set/defaultRule
                             (list 'implies (list bird '?x) (list flies '?x))))
              'UniverseContext)
    (is (v/ask? kb (list isCapital (list CapitalOfFn France) Yes) 'UniverseContext)
        "the conjunct is answerable when it is asked as a goal")
    (is (empty? (v/sentexes-matching kb (list flies '?x) 'UniverseContext))
        "so forward chaining concludes nothing")
    (is (empty? (v/prove kb (list flies '?x) 'UniverseContext))
        "and the DFS proves nothing")
    (is (empty? (binding [v/*query-engine* :inference
                          v/*query-options*  {:max-depth 3}]
                  (v/prove kb (list flies '?x) 'UniverseContext)))
        "and neither does the node engine")))

;; ---- resultGenl + rewriteOf-to-real-term ---------------------------------

(tu/deftest-kb result-genl-materializes-a-subtype-edge
  (tu/with-terms [SubtypeFn Base super]
    (v/assert kb (list 'reifiableFunction SubtypeFn) 'UniverseContext)
    (v/assert kb (list 'genl super 'thing) 'UniverseContext)
    (v/assert kb (list 'resultGenl SubtypeFn super) 'UniverseContext)
    (let [h (v/assert kb (list 'studies 'Alice (list SubtypeFn Base)) 'UniverseContext)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "the minted constant is a subtype of the result type"
        (is (nat/reified-nat-symbol? k))
        (is (v/genl? kb k super))))))

(tu/deftest-kb rewriteof-reifies-a-nat-to-an-existing-real-term
  (tu/with-terms [CapitalFn France Paris]
    (v/assert kb (list 'reifiableFunction CapitalFn) 'UniverseContext)
    ;; (CapitalFn France) should reify to the real Paris, not a fresh constant
    (v/assert kb (list 'rewriteOf Paris (list CapitalFn France)) 'UniverseContext)
    (let [h (v/assert kb (list 'locatedIn (list CapitalFn France) 'Europe) 'UniverseContext)]
      (testing "the NAT resolves to the declared real term"
        (is (= (list 'locatedIn Paris 'Europe) (:sentence (v/sentex kb h))))
        (is (seq (v/sentexes-matching kb (list 'locatedIn (list CapitalFn France) '?where) '?ctx)))))))

;; ---- recover: the reifiable gate + reified NAT data survive a rebuild -----------

(tu/deftest-kb nat-data-survives-recover
  ;; the reifiable prop and the termOfUnit / result-type facts are all durable, so a
  ;; rebuild from the records must reconstruct the gate, dedup, and expansion — else a
  ;; recovered KB would disagree with the running one about what a NAT reifies to.
  ;; `recover` rebuilds the taxonomy + JTMS in place from the store (it adds no
  ;; sentex), so the fixture's net-neutral teardown still restores the baseline.
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiableFunction FruitFn) 'UniverseContext)
    (v/assert kb (list 'resultIsa FruitFn fruit) 'UniverseContext)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'UniverseContext)
          k (k-of kb h)]
      (v/recover kb)
      (testing "the gate, the constant map, and the materialized type all rebuild"
        (is (true? (nat/any-reifiable-functions? kb)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (seq (v/sentexes-matching kb (list fruit k) '?ctx))))
      (testing "a fresh NAT still dedups to the same constant after recovery"
        (let [h2 (v/assert kb (list 'taste (list FruitFn AppleTree) 'Sweet) 'UniverseContext)]
          (is (= k (k-of kb h2))))))))

;; ---- the corresponding predicate -----------------------------------------
;;
;; `(functionCorrespondingPredicate F P N)` says the function and the predicate state
;; one relationship, so the reify reads it **both** ways: an application resolves to
;; the value `P` already names, and a constant minted for want of one is projected
;; back onto `P`.  What the tests below are really about is the seam between those
;; two — whichever of the application, the fact and the declaration lands last, the KB
;; ends up holding one term for one application.

(tu/deftest-kb a-corresponding-fact-names-the-term-an-application-reifies-to
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)
    (v/assert kb (list motherOf Muffet Mary) 'UniverseContext)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'UniverseContext)]
      (testing "the application resolves to the value, and mints nothing beside it"
        (is (= (list caresFor Bob Mary) (:sentence (v/sentex kb h))))
        (is (empty? (v/sentexes-matching kb (list 'termOfUnit '?k (list MotherFn Muffet))
                                         'UniverseContext))))
      (testing "a query written with the application still finds it"
        (is (= [{'?w Bob}] (v/ask kb (list caresFor '?w (list MotherFn Muffet)) '?ctx)))))))

(tu/deftest-kb an-application-with-no-value-mints-a-constant-that-answers-the-predicate
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'UniverseContext)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "no value is known, so the expression mints a placeholder"
        (is (nat/reified-nat-symbol? k)))
      (testing "and the placeholder is projected onto the corresponding predicate"
        (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) '?ctx)))))))

(tu/deftest-kb a-value-arriving-after-the-mint-retires-the-placeholder
  ;; the order-independence case.  The fact and the application say the same thing, so
  ;; whichever lands second must not leave the KB with two values for one application.
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'UniverseContext)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'UniverseContext)
      (testing "one value, and it is the one somebody named"
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) '?ctx))))
      (testing "the use of the placeholder migrated onto it"
        (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx))))
      (testing "and the expression still resolves — to the real term now"
        (is (= Mary (nat/dedup-constant kb (list MotherFn Muffet))))
        (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))))))

(tu/deftest-kb a-declared-position-puts-the-value-where-it-says
  ;; Cyc's own example: (StreetCornerFn XING DIRECTION) = LOT exactly when
  ;; (streetCornerOf LOT XING DIRECTION), so the value is argument 1 and not the last.
  (tu/with-terms [StreetCornerFn streetCornerOf Xing1 North Lot7 ownedBy Alice]
    (v/assert kb (list 'reifiableFunction StreetCornerFn) 'UniverseContext)
    (v/assert kb (list 'functionCorrespondingPredicate StreetCornerFn streetCornerOf 1)
              'UniverseContext)
    (v/assert kb (list streetCornerOf Lot7 Xing1 North) 'UniverseContext)
    (let [h (v/assert kb (list ownedBy (list StreetCornerFn Xing1 North) Alice) 'UniverseContext)]
      (is (= (list ownedBy Lot7 Alice) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-declaration-arriving-last-reconciles-what-was-already-minted
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'UniverseContext)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'UniverseContext)
      (testing "before the declaration the two terms are unrelated"
        (is (= k (nat/dedup-constant kb (list MotherFn Muffet)))))
      (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)
      (testing "declaring it last reaches the state declaring it first would have"
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) '?ctx)))
        (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx)))
        (is (= Mary (nat/dedup-constant kb (list MotherFn Muffet))))))))

(tu/deftest-kb a-declaration-arriving-last-projects-a-placeholder-that-has-no-value
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'UniverseContext)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (empty? (v/ask kb (list motherOf Muffet '?m) '?ctx)))
      (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)
      (testing "the constant minted before the declaration is projected by it"
        (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) '?ctx)))))))

(tu/deftest-kb two-declarations-for-one-function-decide-nothing
  ;; Two correspondences are two different claims about what `(F a…)` denotes.  Choosing
  ;; between them would have to key on a handle, which is the one thing belief may never
  ;; do — so neither is read, and the application mints as if none were declared.
  (tu/with-terms [MotherFn motherOf parentOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn parentOf) 'UniverseContext)
    (v/assert kb (list motherOf Muffet Mary) 'UniverseContext)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'UniverseContext)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (is (not= Mary k))
      (testing "and neither predicate is projected onto"
        (is (empty? (v/ask kb (list parentOf Muffet '?m) '?ctx)))
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) '?ctx)))))))

(tu/deftest-kb retracting-the-declaration-stops-the-application-resolving
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor sees]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (let [d (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)]
      (v/assert kb (list motherOf Muffet Mary) 'UniverseContext)
      (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))
      (v/retract! kb d)
      (testing "the declaration is belief-following, so the reify stops reading it"
        (is (nil? (nat/correspondence-value kb (list MotherFn Muffet))))
        (let [h (v/assert kb (list sees Bob (list MotherFn Muffet)) 'UniverseContext)]
          (is (nat/reified-nat-symbol? (nth (:sentence (v/sentex kb h)) 2))))))))

(tu/deftest-kb an-ill-formed-correspondence-is-refused
  (tu/with-terms [MotherFn motherOf Mary]
    (doseq [[what s] [["one argument"      (list 'functionCorrespondingPredicate MotherFn)]
                      ["four arguments"    (list 'functionCorrespondingPredicate MotherFn motherOf 2 2)]
                      ["an individual"     (list 'functionCorrespondingPredicate MotherFn Mary)]
                      ["a position that is not a positive integer"
                       (list 'functionCorrespondingPredicate MotherFn motherOf 'first)]]]
      (let [e (try (v/assert kb s 'UniverseContext) nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) what)
        (is (= :not-well-formed (:type (ex-data e))) what)))))

(tu/deftest-kb a-correspondence-survives-recover
  ;; the declaration is read through the index rather than a taxonomy cache, so a
  ;; rebuild has nothing to reconstruct — which is the claim worth pinning, since a
  ;; recovered KB that stopped resolving applications would be a restart changing an
  ;; answer.
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)
    (v/assert kb (list motherOf Muffet Mary) 'UniverseContext)
    (v/recover kb)
    (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'UniverseContext)]
      (is (= (list caresFor Bob Mary) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-projection-does-not-keep-an-orphaned-placeholder-alive
  ;; the projection states what the constant *is*, so it is bookkeeping like a result
  ;; type — a constant whose only remaining sentex is its own projection has no live
  ;; use, and treating one as a use would make every placeholder immortal.
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiableFunction MotherFn) 'UniverseContext)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'UniverseContext)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'UniverseContext)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (seq (v/ask kb (list motherOf Muffet '?m) '?ctx)))
      (v/retract! kb h)
      (testing "the placeholder, its map and its projection all go"
        (is (nil? (nat/dedup-constant kb (list MotherFn Muffet))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (v/ask kb (list motherOf Muffet '?m) '?ctx)))
        (is (empty? (nat/orphaned-constants kb)))))))
