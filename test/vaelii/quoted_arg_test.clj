;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quoted-arg-test
  "`(quotedArg pred n type)` — the mention twin of `arg` (docs/argtypes.md).  Where `arg`
  types what an argument *denotes*, `quotedArg` types the argument *as a term*: its EDN
  kind (string, number with integer below it, symbol) checked through genl against a
  syntactic type.  `(quotedArg nameOfGuy 1 string)` refuses `(nameOfGuy 5)` — 5 is a
  number, not a string — and admits `(nameOfGuy \"Bob\")`."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(defn- refusal
  "The violation type `check` predicts for `sentence` in CxUniverse, or nil when it is
  well-formed."
  [kb sentence]
  (:type (first (v/check kb sentence 'CxUniverse))))

(tu/deftest-kb quotedarg-types-an-argument-by-its-literal-kind
  (tu/with-terms [nameOfGuy]
    (v/assert kb (list 'unaryPredicate nameOfGuy) 'CxUniverse)
    (v/assert kb (list 'quotedArg nameOfGuy 1 'string) 'CxUniverse)
    (testing "a string literal satisfies it — and stores"
      (is (nil? (refusal kb (list nameOfGuy "Bob"))))
      (is (some? (v/assert kb (list nameOfGuy "Bob") 'CxUniverse))))
    (testing "a number does not — 5 is not a string as a term"
      (is (= :quoted-arg-type (refusal kb (list nameOfGuy 5)))))
    (testing "nor does a symbol — a name is not a string, whatever it denotes"
      (is (= :quoted-arg-type (refusal kb (list nameOfGuy 'Muffet)))))))

(tu/deftest-kb quotedarg-follows-genl-among-the-syntactic-types
  (tu/with-terms [countOf]
    (v/assert kb (list 'unaryPredicate countOf) 'CxUniverse)
    (v/assert kb (list 'quotedArg countOf 1 'number) 'CxUniverse)
    (testing "an integer is a number, so (quotedArg countOf 1 number) admits it"
      (is (nil? (refusal kb (list countOf 5)))))
    (testing "a string is not a number"
      (is (= :quoted-arg-type (refusal kb (list countOf "five")))))))

(tu/deftest-kb quotedarg-is-open-world-about-a-kind-it-does-not-type
  ;; Every leaf kind a sentence can carry has a name in `checks/syntactic-roots`, so the
  ;; exempt case is the one that is genuinely open rather than merely unnamed: a
  ;; **compound**.  What `(MsrFn 5)` denotes is its function's business — `result`, not
  ;; its syntax — so no syntactic kind would be the right answer and the check stays
  ;; silent, the same open-world floor `arg` gives an argument outside the hierarchy.
  (tu/with-terms [holds MsrFn]
    (v/assert kb (list 'unaryPredicate holds) 'CxUniverse)
    (v/assert kb (list 'quotedArg holds 1 'string) 'CxUniverse)
    (v/assert kb (list 'unreifiableFunction MsrFn) 'CxUniverse)
    (is (nil? (refusal kb (list holds (list MsrFn 5))))
        "a compound is exempt, not convicted")
    (testing "while a kind that does have a name is decided rather than waved through"
      (is (= :quoted-arg-type (refusal kb (list holds :a-keyword))))
      (is (= :quoted-arg-type (refusal kb (list holds true)))))))

(tu/deftest-kb quotedarg-and-arg-are-independent
  ;; `arg` (referent) and `quotedArg` (term) are separate checks on one position: the same
  ;; sentence can satisfy one and violate the other.
  (tu/with-terms [tagOf label]
    (v/assert kb (list 'unaryPredicate tagOf) 'CxUniverse)
    (v/assert kb (list 'genl label 'thing) 'CxUniverse)
    (v/assert kb (list 'arg tagOf 1 'label) 'CxUniverse)          ; the REFERENT must be a label
    (v/assert kb (list 'quotedArg tagOf 1 'string) 'CxUniverse)   ; the TERM must be a string
    (testing "a string literal passes quotedArg but is outside the label hierarchy — arg exempts it open-world"
      (is (nil? (refusal kb (list tagOf "x")))))))

(tu/deftest-kb quotedarg-is-open-world-about-a-non-syntactic-declared-type
  ;; a declared type outside the syntactic lattice (a domain collection, e.g. an imported
  ;; Cyc quoted-type that did not map to string/number/symbol) leaves the constraint
  ;; open-world — the check never convicts a literal against a type it cannot judge.
  (tu/with-terms [speaks agent]
    (v/assert kb (list 'unaryPredicate speaks) 'CxUniverse)
    (v/assert kb (list 'genl agent 'thing) 'CxUniverse)
    (v/assert kb (list 'quotedArg speaks 1 'agent) 'CxUniverse)   ; agent is not a syntactic type
    (is (nil? (refusal kb (list speaks "Bob")))
        "a string against a non-syntactic type is not convicted")
    (is (nil? (refusal kb (list speaks 5)))
        "nor is a number — the constraint is out of quotedArg's domain")))

(tu/deftest-kb one-name-serves-both-readings
  ;; `string` is the KB's only name for text and both declarations read it (docs/
  ;; argtypes.md): `arg` asks what the argument denotes, `quotedArg` what is written
  ;; there.  A string literal denotes itself and so satisfies both; a symbol satisfies
  ;; the first open-world — it may yet name text — and fails the second, which is the
  ;; whole of the difference the two words used to carry between them.
  (tu/with-terms [textOf Muffet SomeDoc]
    (v/assert kb (list 'binaryPredicate textOf) 'CxUniverse)
    (v/assert kb (list 'arg textOf 2 'string) 'CxUniverse)
    (testing "arg exempts a symbol: nothing says what it denotes"
      (is (nil? (refusal kb (list textOf Muffet SomeDoc)))))
    (v/assert kb (list 'quotedArg textOf 2 'string) 'CxUniverse)
    (testing "quotedArg convicts the same sentence — a symbol is not the literal"
      (is (= :quoted-arg-type (refusal kb (list textOf Muffet SomeDoc)))))
    (testing "and a string literal satisfies both at once"
      (is (nil? (refusal kb (list textOf Muffet "some text")))))))

(tu/deftest-kb arg-and-quotedarg-can-type-one-symbol-in-both-registers
  ;; The same written symbol can denote a predicate while being a symbol as syntax.
  ;; `arg` checks the denotation; `quotedArg` checks the written term.  Neither reading
  ;; should erase or contaminate the other.
  (tu/with-terms [testPred parentOf]
    (v/assert kb (list 'unaryPredicate testPred) 'CxUniverse)
    (v/assert kb (list 'binaryPredicate parentOf) 'CxUniverse)
    (v/assert kb (list 'genl 'symbol 'intangible) 'CxUniverse)
    (v/assert kb (list 'arg testPred 1 'predicate) 'CxUniverse)
    (v/assert kb (list 'quotedArg testPred 1 'symbol) 'CxUniverse)
    (is (nil? (refusal kb (list testPred parentOf)))
        (str "parentOf denotes a predicate and is written as a symbol; placing the "
             "syntax kind under intangible does not classify the referent as a symbol"))))

(tu/deftest-kb a-quoted-symbol-is-distinct-from-using-its-denotation
  ;; A different predicate asks for a symbol at the use level.  The bare parentOf denotes
  ;; a predicate and therefore fails that constraint; `(Quote parentOf)` is a compound
  ;; mention and remains WFF.  This pins the boundary without conflating it with the
  ;; preceding predicate's simultaneous arg/quotedArg declarations.
  (tu/with-terms [quotedTestPred parentOf Quote PredicateQuote]
    (v/assert kb (list 'unaryPredicate quotedTestPred) 'CxUniverse)
    (v/assert kb (list 'binaryPredicate parentOf) 'CxUniverse)
    (v/assert kb (list 'arg quotedTestPred 1 'symbol) 'CxUniverse)
    (v/assert kb (list 'unreifiableFunction Quote) 'CxUniverse)
    (v/assert kb (list 'quotingFunction Quote) 'CxUniverse)
    (v/assert kb (list 'result Quote 'symbol) 'CxUniverse)
    (v/assert kb (list 'unreifiableFunction PredicateQuote) 'CxUniverse)
    (v/assert kb (list 'quotingFunction PredicateQuote) 'CxUniverse)
    (v/assert kb (list 'result PredicateQuote 'predicate) 'CxUniverse)
    (is (= :arg-type (refusal kb (list quotedTestPred parentOf)))
        "using parentOf denotes a predicate, not a symbol")
    (is (= :arg-type
           (refusal kb (list quotedTestPred (list PredicateQuote parentOf))))
        "a quoted compound whose declared result is predicate does not satisfy symbol")
    (is (nil? (refusal kb (list quotedTestPred (list Quote parentOf))))
        "Quote declares a symbol result, so the quoted mention satisfies the use-level slot")))
