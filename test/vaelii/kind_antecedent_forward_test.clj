;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kind-antecedent-forward-test
  "Forward rules with a value-kind or expression-kind antecedent: `(string ?x)`,
  `(sentence ?q)` and their neighbours.

  A value kind is computed once another antecedent binds its argument
  (`sentex/deferred-predicates`), and an expression kind read off a quoted form's shape is
  answered with empty support.  Either joins beside a stored fact, which supports the
  firing.  A rule whose only antecedent is a kind fires on nothing: a value-kind one is
  refused, and an expression-kind one rests on no stored fact (docs/argtypes.md, \"What a
  quoted form is\")."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

;; The fixture loads the upper layer, whose reflection.txt holds the expression lattice
;; `sentence` answers in.
(use-fixtures :once (tu/loaded #(doto % (tu/load-core!))))
(use-fixtures :each (tu/neutral))

(def ^:private Quote
  "The engine's `Quote`, the quoting function a `sentence` antecedent reads."
  sx/quote-functor)

(def ^:private cases
  "Each kind beside a value of that kind, as `[kind value]`: the five value kinds
  `EvaluableProver` answers for a literal, `integer`, and a quoted sentence under
  `sentence` and under `formula`, one `genl` edge above it."
  [['string "rex"]
   ['number 2.5]
   ['boolean true]
   ['keyword :rex]
   ['character \r]
   ['integer 5]
   ['sentence (list Quote (list 'not (list 'dog 'Muffet)))]
   ['formula (list Quote (list 'not (list 'dog 'Muffet)))]])

(defn- setup!
  "State what a `sentence` value needs: `Quote` as a function and `dog` as a predicate."
  [kb]
  (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
  (v/assert kb (list 'unary_predicate 'dog) 'CxUniverse))

(defn- fired?
  "Assert `(implies (and (valueOf ?a ?x) (kind ?x)) (kinded ?a))` and `(valueOf Ann
  value)`, the rule first when `rule-first?`, and return whether `(kinded Ann)` is
  stored."
  [kb kind value rule-first?]
  (tu/with-terms [valueOf kinded Ann]
    (let [rule #(v/assert kb (list 'implies (list 'and (list valueOf '?a '?x) (list kind '?x))
                                   (list kinded '?a))
                          'CxUniverse {:direction :forward})
          fact #(v/assert kb (list valueOf Ann value) 'CxUniverse)]
      (if rule-first? (do (rule) (fact)) (do (fact) (rule)))
      (boolean (seq (v/sentexes-matching kb (list kinded Ann) 'CxUniverse))))))

(tu/deftest-kb a-kind-antecedent-on-a-bound-value-fires-in-either-order
  (setup! kb)
  (is (= (into {} (for [[kind _] cases, rule-first? [true false]]
                    [[kind rule-first?] true]))
         (into {} (for [[kind value] cases, rule-first? [true false]]
                    [[kind rule-first?] (fired? kb kind value rule-first?)])))))

(tu/deftest-kb a-kind-antecedent-on-a-value-of-another-kind-does-not-fire
  (setup! kb)
  (is (= #{false}
         (set (for [[kind value] [['string 5] ['number "rex"] ['boolean 0]
                                  ['sentence (list Quote 'Muffet)]]
                    rule-first? [true false]]
                (fired? kb kind value rule-first?))))))

(tu/deftest-kb a-value-kind-of-a-constant-reads-the-stored-fact
  (tu/with-terms [valueOf kinded Ann Label]
    (v/assert kb (list 'implies (list 'and (list valueOf '?a '?x) (list 'string '?x))
                       (list kinded '?a))
              'CxUniverse {:direction :forward})
    (v/assert kb (list valueOf Ann Label) 'CxUniverse)
    (let [stated? #(boolean (seq (v/sentexes-matching kb (list kinded Ann) 'CxUniverse)))
          before  (stated?)
          h       (v/assert kb (list 'string Label) 'CxUniverse)
          with    (stated?)]
      (v/retract! kb h)
      (is (= [false true false] [before with (stated?)])))))

(tu/deftest-kb a-rule-whose-only-antecedent-is-a-kind-does-not-fire
  (setup! kb)
  (testing "a value kind reads a variable no antecedent binds, so the rule is refused"
    (tu/with-terms [kinded]
      (is (= #{:naf-not-closed}
             (set (for [kind '[string number boolean keyword character]]
                    (try (v/assert kb (list 'implies (list kind '?x) (list kinded '?x))
                                   'CxUniverse {:direction :forward})
                         nil
                         (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))))
  (testing "an expression kind read off the form's shape supports nothing"
    (tu/with-terms [valueOf kinded Ann]
      (let [q (list Quote (list 'not (list 'dog 'Muffet)))]
        (v/assert kb (list 'implies (list 'sentence '?x) (list kinded '?x))
                  'CxUniverse {:direction :forward})
        (v/assert kb (list 'implies (list 'sentence q) (list kinded Ann))
                  'CxUniverse {:direction :forward})
        (v/assert kb (list valueOf Ann q) 'CxUniverse)
        ;; Asked of this test's own two terms: the KB holds other sentence-typed terms, a
        ;; rule quoted in a `declined_rule_macro` fact among them, and those are not what
        ;; this reads.
        (is (empty? (v/sentexes-matching kb (list kinded q) 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb (list kinded Ann) 'CxUniverse)))))))

(tu/deftest-kb a-firing-on-a-kind-antecedent-is-withdrawn-with-the-fact-that-bound-it
  (setup! kb)
  (is (= (zipmap (map first cases) (repeat [true false]))
         (into {} (for [[kind value] cases]
                    (tu/with-terms [valueOf kinded Ann]
                      (v/assert kb (list 'implies (list 'and (list valueOf '?a '?x)
                                                        (list kind '?x))
                                         (list kinded '?a))
                                'CxUniverse {:direction :forward})
                      (let [stated? #(boolean (seq (v/sentexes-matching kb (list kinded Ann)
                                                                        'CxUniverse)))
                            h       (v/assert kb (list valueOf Ann value) 'CxUniverse)
                            with    (stated?)]
                        (v/retract! kb h)
                        [kind [with (stated?)]])))))))
