;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quoted-arg-test
  "`(quotedArg pred n type)` — the mention twin of `arg` (docs/argtypes.md).  Where `arg`
  types what an argument *denotes*, `quotedArg` types the argument *as a term*: its EDN
  kind (string, number with integer below it, symbol) checked through genl against a
  syntactic type, and a compound's expression kinds checked for a separation from it.  Under `(quotedArg name_of_guy 1 string)`, `assert` stores
  `(name_of_guy 5)` inert — 5 is a number, not a string — `try-assert` refuses it, and
  `(name_of_guy \"Bob\")` is believed."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- refusal
  "The violation `try-assert` refuses `sentence` with in CxUniverse (a
  `:definitional-clash`'s `:violation`), or nil when it stores it, retracting what it
  stored."
  [kb sentence]
  (try (some->> (v/try-assert kb sentence 'CxUniverse) (v/retract! kb)) nil
       (catch clojure.lang.ExceptionInfo e
         (let [d (ex-data e)] (or (:violation d) (:type d))))))

(tu/deftest-kb quotedarg-types-an-argument-by-its-literal-kind
  (tu/with-terms [name_of_guy]
    (v/assert kb (list 'unary_predicate name_of_guy) 'CxUniverse)
    (v/assert kb (list 'quotedArg name_of_guy 1 'string) 'CxUniverse)
    (testing "a string value satisfies it — and stores"
      (is (nil? (refusal kb (list name_of_guy "Bob"))))
      (is (some? (v/assert kb (list name_of_guy "Bob") 'CxUniverse))))
    (testing "a number does not — 5 is not a string as a term"
      (is (= :quoted-arg-type (refusal kb (list name_of_guy 5)))))
    (testing "nor does a symbol — a name is not a string, whatever it denotes"
      (is (= :quoted-arg-type (refusal kb (list name_of_guy 'Muffet)))))))

(tu/deftest-kb quotedarg-follows-genl-among-the-syntactic-types
  (tu/with-terms [countOf]
    (v/assert kb (list 'unary_predicate countOf) 'CxUniverse)
    (v/assert kb (list 'quotedArg countOf 1 'number) 'CxUniverse)
    (testing "an integer is a number, so (quotedArg countOf 1 number) admits it"
      (is (nil? (refusal kb (list countOf 5)))))
    (testing "a string is not a number"
      (is (= :quoted-arg-type (refusal kb (list countOf "five")))))))

(tu/deftest-kb quotedarg-decides-every-leaf-kind
  ;; every leaf kind a sentence can carry has a name in `checks/syntactic-roots`
  (tu/with-terms [holds]
    (v/assert kb (list 'unary_predicate holds) 'CxUniverse)
    (v/assert kb (list 'quotedArg holds 1 'string) 'CxUniverse)
    (is (= :quoted-arg-type (refusal kb (list holds :a-keyword))))
    (is (= :quoted-arg-type (refusal kb (list holds true))))))

(tu/deftest-kb a-compound-is-held-only-where-one-of-its-kinds-is-separated-from-the-type
  ;; a compound's kinds are its spelling's (`provers/shape-kinds`): `(MsrFn 5)` is a
  ;; closed non_atomic_expression, which neither reaches non_atomic_term nor is separated
  ;; from it, and `(not (dog Fido))` is a sentence, which reflection.txt separates from
  ;; non_atomic_term.  Each row runs in both arrival orders of {declaration, fact}.
  (doseq [[t compound held] [['string          '(MsrFn 5)          :quoted-arg-type]
                             ['symbol          '(MsrFn 5)          :quoted-arg-type]
                             ['non_atomic_term '(MsrFn 5)          nil]
                             ['formula         '(MsrFn 5)          nil]
                             ['non_atomic_term '(not (dog Fido))   :quoted-arg-type]
                             ['sentence        '(not (dog Fido))   nil]]
          decl-first? [true false]]
    (tu/with-terms [holds MsrFn dog Fido]
      (v/assert kb (list 'unreifiable_function MsrFn) 'CxUniverse)
      (let [d    (list 'quotedArg holds 1 t)
            fact (list holds (walk/postwalk-replace {'MsrFn MsrFn 'dog dog 'Fido Fido} compound))]
        (v/assert kb (list 'unary_predicate holds) 'CxUniverse)
        (doseq [s (if decl-first? [d fact] [fact d])] (v/assert kb s 'CxUniverse))
        (testing (str t " " compound (if decl-first? ", declaration first" ", fact first"))
          (is (= held (some #(when (= fact (:sentence %)) (get-in % [:detail :type]))
                            (v/violations kb))))
          (is (= (nil? held) (v/ask? kb fact 'CxUniverse))))))))

(tu/deftest-kb quotedarg-and-arg-are-independent
  ;; the entailing reading: the derivation is the subject
  (tu/with-entailing
    ;; `arg` (referent) and `quotedArg` (term) are separate checks on one position: the same
    ;; sentence can satisfy one and violate the other.
    (tu/with-terms [tagOf label]
      (v/assert kb (list 'unary_predicate tagOf) 'CxUniverse)
      (v/assert kb (list 'genl label 'thing) 'CxUniverse)
      (v/assert kb (list 'arg tagOf 1 label) 'CxUniverse)          ; the REFERENT must be a label
      (v/assert kb (list 'quotedArg tagOf 1 'string) 'CxUniverse)   ; the TERM must be a string
      (testing "a string value passes quotedArg and fails arg: the declaration derives
              `label` a type, and a string is not one"
        (is (= :arg-type (refusal kb (list tagOf "x"))))))))

(tu/deftest-kb quotedarg-is-open-world-about-a-non-syntactic-declared-type
  ;; a declared type outside the syntactic lattice (a domain collection, e.g. an imported
  ;; Cyc quoted-type that did not map to string/number/symbol) leaves the constraint
  ;; open-world — the check never convicts a literal against a type it cannot judge.
  (tu/with-terms [speaks agent]
    (v/assert kb (list 'unary_predicate speaks) 'CxUniverse)
    (v/assert kb (list 'genl agent 'thing) 'CxUniverse)
    (v/assert kb (list 'quotedArg speaks 1 agent) 'CxUniverse)   ; agent is not a syntactic type
    (is (nil? (refusal kb (list speaks "Bob")))
        "a string against a non-syntactic type is not convicted")
    (is (nil? (refusal kb (list speaks 5)))
        "nor is a number — the constraint is out of quotedArg's domain")))

(tu/deftest-kb one-name-serves-both-readings
  ;; `string` is the KB's only name for text and both declarations read it (docs/
  ;; argtypes.md): `arg` asks what the argument denotes, `quotedArg` what is written
  ;; there.  A string value denotes itself and so satisfies both; a symbol satisfies
  ;; the first open-world — it may yet name text — and fails the second, which is the
  ;; whole of the difference the two words used to carry between them.
  (tu/with-terms [textOf Muffet SomeDoc]
    (v/assert kb (list 'binary_predicate textOf) 'CxUniverse)
    (v/assert kb (list 'arg textOf 2 'string) 'CxUniverse)
    (testing "arg exempts a symbol: nothing says what it denotes"
      (is (nil? (refusal kb (list textOf Muffet SomeDoc)))))
    (v/assert kb (list 'quotedArg textOf 2 'string) 'CxUniverse)
    (testing "quotedArg convicts the same sentence — a symbol is not the literal"
      (is (= :quoted-arg-type (refusal kb (list textOf Muffet SomeDoc)))))
    (testing "and a string value satisfies both at once"
      (is (nil? (refusal kb (list textOf Muffet "some text")))))))

(tu/deftest-kb arg-and-quotedarg-can-type-one-symbol-in-both-registers
  ;; The same written symbol can denote a predicate while being a symbol as syntax.
  ;; `arg` checks the denotation; `quotedArg` checks the written term.  Neither reading
  ;; should erase or contaminate the other.
  (tu/with-terms [testPred parentOf]
    (v/assert kb (list 'unary_predicate testPred) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list 'genl 'symbol 'intangible) 'CxUniverse)
    (v/assert kb (list 'arg testPred 1 'predicate) 'CxUniverse)
    (v/assert kb (list 'quotedArg testPred 1 'symbol) 'CxUniverse)
    (is (nil? (refusal kb (list testPred parentOf)))
        (str "parentOf denotes a predicate and is written as a symbol; placing the "
             "syntax kind under intangible does not classify the referent as a symbol"))))

(tu/deftest-kb a-quoted-symbol-is-distinct-from-using-its-denotation
  ;; A different predicate asks for a symbol at the use level.  The bare parentOf denotes
  ;; a predicate and therefore fails that constraint; `(Quote parentOf)` is a compound
  ;; mention and remains WFF.  This asserts the boundary without conflating it with the
  ;; preceding predicate's simultaneous arg/quotedArg declarations.
  ;; Forced to the constraint reading: the contrast is between the quoted arm's verdict and
  ;; the ordinary one's, and with the entailment on the ordinary arm mints rather than
  ;; convicts (docs/argtypes.md).  The quoted arm is unchanged by the toggle.
  (tu/without-entailing
   (tu/with-terms [quotedTestPred parentOf]
     (v/assert kb (list 'unary_predicate quotedTestPred) 'CxUniverse)
     (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
     (v/assert kb (list 'arg quotedTestPred 1 'symbol) 'CxUniverse)
     (v/assert kb (list 'unreifiable_function 'Quote) 'CxUniverse)
     (v/assert kb (list 'result 'Quote 'symbol) 'CxUniverse)
     ;; `Quasiquote` is the other quoting function; no `unreifiable_function` mark, so the
     ;; quasiquote reducer stays off and the mention reaches the check as written
     (v/assert kb (list 'result 'Quasiquote 'predicate) 'CxUniverse)
     (is (= :arg-type (refusal kb (list quotedTestPred parentOf)))
         "using parentOf denotes a predicate, not a symbol")
     (is (= :arg-type
            (refusal kb (list quotedTestPred (list 'Quasiquote parentOf))))
         "a quoted compound whose declared result is predicate does not satisfy symbol")
     (is (nil? (refusal kb (list quotedTestPred (list 'Quote parentOf))))
         "Quote declares a symbol result, so the quoted mention satisfies the use-level slot"))))

(tu/deftest-kb a-quotedarg-violation-is-inert-in-either-order
  (tu/with-terms [holds]
    (doseq [arg [5 'Muffet]]
      (let [decl (list 'quotedArg holds 1 'string)
            fact (list holds arg)
            read (fn [order]
                   (let [hs (mapv #(v/assert kb % 'CxUniverse)
                                  (cons (list 'unary_predicate holds)
                                        (map {:decl decl :fact fact} order)))
                         h  (v/handle-of kb fact 'CxUniverse)
                         r  [(some? h) (v/believed? kb h 'CxUniverse)
                             (-> (v/why-not kb fact 'CxUniverse) :conviction :type)
                             (into [] (comp (filter #(= :inert-argument (:violation %)))
                                            (map (juxt :sentence (comp :type :detail))))
                                   (v/violations kb))]]
                     (doseq [h (rseq hs)] (v/retract! kb h))
                     r))]
        (is (= #{[true false :quoted-arg-type [[fact :quoted-arg-type]]]}
               (into #{} (map read) [[:decl :fact] [:fact :decl]]))
            (str arg " is stored, held and reported in both orders"))))
    (let [hs (mapv #(v/assert kb % 'CxUniverse)
                   [(list 'unary_predicate holds) (list holds 5) (list 'quotedArg holds 1 'string)
                    (list holds "x")])]
      (is (v/believed? kb (peek hs) 'CxUniverse) "a string stays believed")
      (v/retract! kb (nth hs 2))
      (is (v/believed? kb (nth hs 1) 'CxUniverse) "the declaration's retraction releases 5")
      (doseq [h (rseq (assoc hs 2 nil)) :when h] (v/retract! kb h)))))

(tu/deftest-kb a-quantifier-binds-an-open-expression-taken-as-written
  ;; Position 1 of a quantifier holds the variable it binds, or a sequence of them, as
  ;; written.  A variable is open in itself and a sequence of variables has one free, so
  ;; each is an open_expression; a constant is closed.  A quantifier is never stored, and
  ;; a constant written as its binder is refused as not well-formed before any argument
  ;; check runs, so the declaration is read here through the kinds it names.
  (doseq [q '[forall thereExists exists]]
    (is (true? (v/ask? kb (list 'quotedArg q 1 'open_expression) 'CxUniverse))
        (str q " types its binder an open_expression"))
    (is (empty? (filter #(= q (:predicate %))
                        (:missing-arg (v/kb-integrity kb #{} 'CxUniverse {:categories #{:missing-arg}
                                                                          :max-results 10000}))))
        (str "kb-integrity reports no position of " q " untyped")))
  (is (true? (v/ask? kb '(open_expression (Quote ?x)) 'CxUniverse)) "one variable")
  (is (true? (v/ask? kb '(open_expression (Quote (?x ?y))) 'CxUniverse)) "a sequence of variables")
  (is (not (v/ask? kb '(open_expression (Quote Muffet)) 'CxUniverse)) "a constant is not open")
  (is (true? (v/ask? kb '(closed_expression (Quote Muffet)) 'CxUniverse))
      "and is a closed_expression, disjoint from it"))
