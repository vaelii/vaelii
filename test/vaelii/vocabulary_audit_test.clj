;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.vocabulary-audit-test
  "Declared and enforced, against declared and ignored.

  Nothing about a declaration's *shape* says whether anything reads it.
  `(maxCardinality parentOf 2)` is a well-formed ternary fact, storable, believed, and
  read by nobody — so a KB author gets identical silence from a constraint that is
  enforced and one that was never implemented.  `vaelii.impl.vocabulary` answers the
  question for the engine's own grammar, and these tests are what keep the answer true:
  a term `CxCore` declares that the roster says nothing about fails here, and so
  does a roster entry naming a term the grammar has retired.

  A CxCore baseline is the whole population, which is why this is its own namespace
  — the constraint tests beside it (`constraint-vocabulary-test`) need a cleared KB."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.vocabulary :as vocab]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(tu/deftest-kb every-term-the-grammar-declares-is-classified
  ;; The durable half.  A functor added to CxCore without anybody deciding whether
  ;; the engine reads it lands in `:unclassified`, and this fails — which is the whole
  ;; point: `interArg` sat in the design notes as a plausible declaration for as long
  ;; as nothing was checking.
  (let [a (v/vocabulary-audit kb)]
    (is (empty? (:unclassified a))
        "a term CxCore declares that vocabulary/roster says nothing about")
    (is (empty? (:retired a))
        "a roster entry naming a term CxCore no longer declares")
    (is (empty? (:contradicted a))
        "a term the special-predicate table gives an arm to and the roster calls inert")
    (is (seq (:enforced a)))
    (is (seq (:inert a)) "and the inert set is not empty — that is the honest answer")))

(tu/deftest-kb a-new-grammar-declaration-nobody-classified-is-reported
  ;; The test above only fails if this mechanism works, so drive it: a term added to the
  ;; grammar shows up unclassified rather than passing quietly.
  (tu/with-terms [maxCardinality]
    (v/assert kb (list 'comment maxCardinality "a plausible-looking declaration")
              'CxCore)
    (is (= [maxCardinality] (:unclassified (v/vocabulary-audit kb))))))

;; `the-special-predicate-table-and-the-roster-agree` stood here and is gone.  It walked
;; `special/entries` asserting no functor with an arm was classified inert — which is
;; `audit`'s `:contradicted` restated, and the test above already asserts that empty.  The
;; half of it that was about two hand-written lists agreeing went with the roster: the
;; prose now sits on the term's own declaration and the class is read off that entry's
;; facets, so there is no second list for the table to disagree with.

(tu/deftest-kb the-two-new-constraints-are-on-the-enforced-side
  ;; Ties the implementations in `constraint-vocabulary-test` to the roster, so removing
  ;; one and leaving the claim is a failing test rather than a stale sentence.
  (is (:enforced (v/interpreted 'interArg)))
  (is (:enforced (v/interpreted 'arity)))
  (is (nil? (v/interpreted 'maxCardinality))
      "a term the grammar does not declare is out of scope, not answered")
  (is (:inert (v/interpreted 'typeToInstancePred))
      "and a declared term nothing reads says so rather than reading as enforced"))

(deftest the-roster-answers-in-exactly-one-of-the-two-classes
  (doseq [[term entry] vocab/roster]
    (is (= 1 (count (select-keys entry [:enforced :inert])))
        (str term " must be enforced or inert, and say which"))
    (is (seq (or (:enforced entry) (:inert entry)))
        (str term " carries no reason"))))

;; The same question one layer in: not "does anybody read this declaration" but "does
;; every declaration the settle enrols get read the same way twice".  #45 is what these
;; two are about — `functional`, `asymmetric` and `anti_transitive` were spelled out at
;; four executable sites of `settle.clj` in three spellings, so `functionalInArg` landed
;; in none of them and a sweep naming it everywhere changed nothing.  A mark the roster
;; holds and a pass does not read is the failure this namespace exists for, wearing a
;; different hat: the KB believes a definitional contradiction and reports nothing,
;; which is indistinguishable from having no clash at all.

(deftest every-clash-declaration-functor-carries-a-reach
  (let [marks      @#'settle/definitional-marks
        kinds      @#'settle/clash-declaration-kinds
        functors   @#'settle/clash-declaration-functors
        by-functor @#'settle/clash-declaration-kind]
    (is (= functors (set (keys by-functor)))
        "a functor enrolled as a clash declaration with no kind sweeps nothing silently")
    (is (= (count functors) (reduce + (map count (vals kinds))))
        "the kinds partition: a functor in two makes which reach runs an ordering question")
    ;; #54: the reach roster is a superset of the pairing table, not a copy of it.  Every
    ;; definitional mark must reach as itself — that is the half #45 filed, and deriving
    ;; the reach from a hand-written second list is what it forbids — but the *functional
    ;; family* is wider than the pairing table, which pairs a functor with the prop key it
    ;; stores under and so cannot hold `functionalInArg`, whose table is keyed `[pred n]`.
    ;; That mark reaches stored content in exactly the same way and is enrolled by name.
    (is (set/subset? (set (map first marks)) (:predicate-marked kinds))
        "the definitional marks reach as themselves, not as a second list beside the roster")
    (is (contains? (:predicate-marked kinds) 'functionalInArg)
        (str "the generalized functional mark reaches too — left out, a declaration"
             " arriving after an unmergeable pair convicts nothing, where (functional P)"
             " in the same order convicts"))
    (is (= (into (set (map first marks)) '#{functionalInArg}) (:predicate-marked kinds))
        "and nothing else is in there — a new functor is a deliberate roster change")
    (is (= (set (map second marks)) @#'settle/definitional-mark-keywords)
        "and both spellings of every mark come from the one table of pairs")))

(tu/deftest-kb the-clash-fingerprint-moves-for-every-definitional-mark
  ;; `clash-vocabulary` decides whether a memoized clash answer still holds.  A mark it
  ;; does not fingerprint reads as *nothing that decides clash-ness has moved* while
  ;; that mark's declarations arrive, so the memo answers from before the KB said
  ;; anything about them.
  (doseq [[functor _] @#'settle/definitional-marks]
    (tu/with-terms [CxMark holdsFor]
      (let [before (#'settle/clash-vocabulary (reasoning/taxonomy kb))]
        (v/assert kb (list functor holdsFor) CxMark)
        (is (not= before (#'settle/clash-vocabulary (reasoning/taxonomy kb)))
            (str functor " must move the clash-vocabulary fingerprint"))))))
