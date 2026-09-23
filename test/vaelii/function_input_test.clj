;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.function-input-test
  "A function's own argument declarations, read over the inputs written inside an
  application (docs/argtypes.md).  `(arg InputGapFn 1 integer)` constrains what every
  application of `InputGapFn` is given, so `(observes (InputGapFn \"x\"))` is refused
  whatever `InputGapFn`'s `result` says about what the application denotes.  Both readings
  run: the application is typed by its result where it sits, and its inputs by its
  function's declarations inside it."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(defn- problem
  "The first problem `check` predicts for `sentence` in `context`, or nil."
  ([kb sentence] (problem kb sentence 'CxUniverse))
  ([kb sentence context] (first (v/check kb sentence context))))

(defn- refusal
  "The `:type` of that problem, or nil."
  ([kb sentence] (:type (problem kb sentence)))
  ([kb sentence context] (:type (problem kb sentence context))))

(defn- ex-type
  "The `:type` of the ex-info `f` throws, or nil when it returns."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- declare-gap-fn!
  "The #78 repro's declarations: an unreifiable unary function whose input must be an
  integer and whose application is a `thing`, and a unary predicate over things."
  [kb f observer]
  (doseq [s [(list 'unreifiable_function f)
             (list 'unary_function f)
             (list 'arg f 1 'integer)
             (list 'result f 'thing)
             (list 'unary_predicate observer)
             (list 'arg observer 1 'thing)]]
    (v/assert kb s 'CxUniverse)))

(tu/deftest-kb a-functions-input-declaration-is-read-inside-its-application
  (tu/with-terms [InputGapFn inputGapObserver]
    (declare-gap-fn! kb InputGapFn inputGapObserver)
    (testing "the #78 repro: a string where the function takes an integer"
      (let [p (problem kb (list inputGapObserver (list InputGapFn "not-an-integer")))]
        (is (= :arg-type (:type p)))
        (is (= "not-an-integer" (:arg p)))
        (is (= 'integer (:expected p)))
        (is (= 1 (:position p)) "the position is the function's")
        (is (= (list InputGapFn "not-an-integer") (:application p)))
        (is (re-find #"inside \(" (:message p)) "the message says where the input sits")))
    (testing "assert refuses what check predicts"
      (is (= :arg-type
             (ex-type #(v/assert kb (list inputGapObserver (list InputGapFn "not-an-integer"))
                                 'CxUniverse)))))
    (testing "the well-typed sibling is silent, and stores"
      (is (nil? (problem kb (list inputGapObserver (list InputGapFn 5)))))
      (is (some? (v/assert kb (list inputGapObserver (list InputGapFn 5)) 'CxUniverse))))))

(tu/deftest-kb the-descent-reaches-every-depth
  (tu/with-terms [InputGapFn WrapFn inputGapObserver]
    (declare-gap-fn! kb InputGapFn inputGapObserver)
    (v/assert kb (list 'unreifiable_function WrapFn) 'CxUniverse)
    (v/assert kb (list 'unary_function WrapFn) 'CxUniverse)
    (v/assert kb (list 'result WrapFn 'thing) 'CxUniverse)
    (testing "an ill-typed input two applications down is found"
      (let [p (problem kb (list inputGapObserver (list WrapFn (list InputGapFn "x"))))]
        (is (= :arg-type (:type p)))
        (is (= (list InputGapFn "x") (:application p)) "the innermost application is named")))
    (testing "and a well-typed one is not"
      (is (nil? (problem kb (list inputGapObserver (list WrapFn (list InputGapFn 7)))))))))

(tu/deftest-kb result-typing-and-input-checking-are-separate-readings
  ;; the outer application is typed by its result where it sits; its inputs by its
  ;; function's declarations inside it.  Each convicts on its own grounds.
  (tu/with-terms [InputGapFn inputGapObserver wantsDog dog]
    (declare-gap-fn! kb InputGapFn inputGapObserver)
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate wantsDog) 'CxUniverse)
    (v/assert kb (list 'arg wantsDog 1 dog) 'CxUniverse)
    (testing "well-typed inputs do not rescue an application whose result misses"
      (let [p (problem kb (list wantsDog (list InputGapFn 5)))]
        (is (= :arg-type (:type p)))
        (is (nil? (:application p)) "the result reading's conviction, at the top level")
        (is (re-find #"results in a thing" (:message p)))))
    (testing "and a result that reaches does not excuse an ill-typed input"
      (is (= (list InputGapFn "x")
             (:application (problem kb (list inputGapObserver (list InputGapFn "x")))))))))

(tu/deftest-kb a-nested-symbol-input-is-read-open-world
  ;; the constraint reading: a symbol with no visible type is no evidence, one whose
  ;; types visibly miss the declared one is convicted.  No mint is drawn for a nested
  ;; input under the assertive reading — a declaration arriving later could not find the
  ;; application to mint over, so the mint would depend on arrival order.
  (tu/with-terms [MotherFn likes animal rock Rex Pebble Unknown]
    (doseq [s [(list 'genl animal 'thing) (list 'genl rock 'thing)
               (list 'unreifiable_function MotherFn) (list 'unary_function MotherFn)
               (list 'arg MotherFn 1 animal)
               (list 'unary_predicate likes)]]
      (v/assert kb s 'CxUniverse))
    (v/assert kb (list animal Rex) 'CxUniverse)
    (v/assert kb (list rock Pebble) 'CxUniverse)
    (testing "an input of the declared type passes"
      (is (nil? (problem kb (list likes (list MotherFn Rex))))))
    (testing "an untyped input is not evidence"
      (is (nil? (problem kb (list likes (list MotherFn Unknown))))))
    (testing "an input typed outside the declared type is convicted"
      (is (= :arg-type (refusal kb (list likes (list MotherFn Pebble))))))
    (testing "storing the untyped one mints nothing about it"
      (v/assert kb (list likes (list MotherFn Unknown)) 'CxUniverse)
      (is (not (v/ask? kb (list animal Unknown) 'CxUniverse))))))

(tu/deftest-kb a-functions-genlarg-and-quotedarg-are-read-too
  (tu/with-terms [KindFn NameFn tagged animal dog rock Rex]
    (doseq [s [(list 'genl animal 'thing) (list 'genl dog animal) (list 'genl rock 'thing)
               (list 'unreifiable_function KindFn) (list 'unary_function KindFn)
               (list 'genlArg KindFn 1 animal)
               (list 'unreifiable_function NameFn) (list 'unary_function NameFn)
               (list 'quotedArg NameFn 1 'string)
               (list 'unary_predicate tagged)]]
      (v/assert kb s 'CxUniverse))
    (v/assert kb (list animal Rex) 'CxUniverse)
    (testing "genlArg: a kind below the declared one passes, one outside it is convicted"
      (is (nil? (problem kb (list tagged (list KindFn dog)))))
      (is (= :arg-genl (refusal kb (list tagged (list KindFn rock))))))
    (testing "genlArg: an individual can never be a subtype"
      (is (= :arg-genl (refusal kb (list tagged (list KindFn Rex))))))
    (testing "quotedArg: the input is typed as the term written"
      (is (nil? (problem kb (list tagged (list NameFn "Bob")))))
      (is (= :quoted-arg-type (refusal kb (list tagged (list NameFn 5))))))))

(tu/deftest-kb a-mention-is-not-descended-into
  ;; a position `quotedArg` types holds the term written there, and a quoting function's
  ;; argument is a mention: in both, an application is syntax, and what its function
  ;; declares about the inputs of the applications it is used in does not reach it.
  (tu/with-terms [InputGapFn inputGapObserver holds Quote]
    (declare-gap-fn! kb InputGapFn inputGapObserver)
    (v/assert kb (list 'unary_predicate holds) 'CxUniverse)
    (v/assert kb (list 'quotedArg holds 1 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
    (v/assert kb (list 'quoting_function Quote) 'CxUniverse)
    (v/assert kb (list 'unary_function Quote) 'CxUniverse)
    (testing "a quotedArg position is exempt"
      (is (nil? (problem kb (list holds (list InputGapFn "x"))))))
    (testing "so is a quoting function's argument"
      (is (nil? (problem kb (list inputGapObserver (list Quote (list InputGapFn "x")))))))
    (testing "and so is a quoting predicate's"
      (tu/with-terms [K]
        (is (nil? (problem kb (list 'termOfUnit K (list InputGapFn "x")))))))))

(tu/deftest-kb the-inputs-are-read-from-the-asking-contexts-vantage
  (tu/with-terms [InputGapFn inputGapObserver CxSeen CxBelow CxSibling]
    (doseq [s [(list 'unreifiable_function InputGapFn) (list 'unary_function InputGapFn)
               (list 'result InputGapFn 'thing)
               (list 'unary_predicate inputGapObserver)
               (list 'genlCx CxSeen 'CxUniverse) (list 'genlCx CxSibling 'CxUniverse)
               (list 'genlCx CxBelow CxSeen)]]
      (v/assert kb s 'CxUniverse))
    (v/assert kb (list 'arg InputGapFn 1 'integer) CxSeen)
    (let [s (list inputGapObserver (list InputGapFn "x"))]
      (testing "the context the declaration is written in is refused by it"
        (is (= :arg-type (refusal kb s CxSeen))))
      (testing "a context below it inherits the declaration"
        (is (= :arg-type (refusal kb s CxBelow))))
      (testing "a sibling that cannot see it is not refused"
        (is (nil? (problem kb s CxSibling)))))))

(tu/deftest-kb the-predicates-own-readings-are-unchanged
  ;; the top level reads what it always read, with the same message: the nested arm adds
  ;; a reading and replaces none.
  (tu/with-terms [countOf]
    (v/assert kb (list 'unary_predicate countOf) 'CxUniverse)
    (v/assert kb (list 'arg countOf 1 'integer) 'CxUniverse)
    (let [p (problem kb (list countOf "x"))]
      (is (= :arg-type (:type p)))
      (is (nil? (:application p)))
      (is (not (re-find #"inside" (:message p)))))
    (is (nil? (problem kb (list countOf 3))))))

(tu/deftest-kb a-derived-conclusion-is-held-to-the-inputs-too
  ;; the derivation path asks the same checks, so a rule concluding an application with an
  ;; ill-typed input places nothing, and the well-typed firing is placed
  (tu/with-terms [InputGapFn inputGapObserver source]
    (declare-gap-fn! kb InputGapFn inputGapObserver)
    (v/assert kb (list 'unary_predicate source) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list source '?x) (list inputGapObserver (list InputGapFn '?x))))
              'CxUniverse)
    (v/assert kb (list source 5) 'CxUniverse)
    (v/assert kb (list source "x") 'CxUniverse)
    (is (v/ask? kb (list inputGapObserver (list InputGapFn 5)) 'CxUniverse))
    (is (not (v/ask? kb (list inputGapObserver (list InputGapFn "x")) 'CxUniverse)))))

(tu/deftest-kb a-reifiable-applications-inputs-are-read-before-it-is-minted
  ;; `assert` mints a ground reifiable application into a constant before the checks run,
  ;; and the constant carries the function's result types, not its inputs — so the inputs
  ;; are read over the sentence as written, first.  `check` does not mint and reads them
  ;; structurally; the two agree, and a refusal leaves no constant behind.
  (tu/with-terms [ReifGapFn inputGapObserver CxSeen]
    (doseq [s [(list 'reifiable_function ReifGapFn) (list 'unary_function ReifGapFn)
               (list 'arg ReifGapFn 1 'integer) (list 'result ReifGapFn 'thing)
               (list 'unary_predicate inputGapObserver) (list 'arg inputGapObserver 1 'thing)
               (list 'genlCx CxSeen 'CxUniverse)]]
      (v/assert kb s 'CxUniverse))
    (let [minted (fn [e] (seq (v/sentexes-matching kb (list 'termOfUnit '?k e) 'CxUniverse)))
          bad    (list inputGapObserver (list ReifGapFn "x"))]
      (testing "check predicts the refusal"
        (is (= :arg-type (refusal kb bad))))
      (testing "assert refuses it, and mints nothing for the refused application"
        (is (= :arg-type (ex-type #(v/assert kb bad 'CxUniverse))))
        (is (nil? (minted (list ReifGapFn "x")))))
      (testing "an (ist Ctx S) is S read in Ctx"
        (is (= :arg-type (ex-type #(v/assert kb (list 'ist CxSeen bad) 'CxUniverse)))))
      (testing "the well-typed sibling stores, through the constant it mints"
        (is (nil? (problem kb (list inputGapObserver (list ReifGapFn 5)))))
        (is (some? (v/assert kb (list inputGapObserver (list ReifGapFn 5)) 'CxUniverse)))
        (is (some? (minted (list ReifGapFn 5))))))))

(tu/deftest-kb a-formula-in-an-argument-position-is-not-an-application
  ;; a genuine negation reaches the checks whole, and its argument is a sentence about a
  ;; predicate's tuples; so is a compound whose head the KB knows as a predicate.  Neither
  ;; is a function applied to terms, and neither is read as one.
  (tu/with-terms [countOf mentions]
    (v/assert kb (list 'unary_predicate countOf) 'CxUniverse)
    (v/assert kb (list 'arg countOf 1 'integer) 'CxUniverse)
    (v/assert kb (list 'unary_predicate mentions) 'CxUniverse)
    (testing "a negation's body is not typed by its predicate's declarations"
      (is (nil? (problem kb (list 'not (list countOf "x"))))))
    (testing "nor is a predicate-headed compound in an argument position"
      (is (nil? (problem kb (list mentions (list countOf "x"))))))))
