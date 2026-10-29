;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rule-variable-arg-test
  "The argument constraints a rule's own variables carry, checked against each other.

  `args-problem` reads a ground argument, and every argument of a rule is a variable, so
  it passes over all of them vacuously.  Without the arm below, a rule whose binding
  chain feeds an impossible term into a position fires believed, and each conclusion is
  convicted one at a time, by a complaint naming the conclusion and never the rule.
  `checks/variable-clash-problem` holds the positions a variable stands in to each other
  instead: `assert` stores a rule it convicts and holds it inert as `:arg-variable`, in
  every arrival order of the rule and its declarations, and `try-assert` refuses it.

  Two arms, and the second is the one that needs saying: a position a `genlArg` names asks
  for a `unary_predicate`, and every position of a `type_relation_predicate` asks for what
  its `args` declaration names, `predicate` from core.txt.  That second half is what
  constrains `genl`'s arguments, the positions in CxUniverse's schema carrying no
  position declaration of their own."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- refusal
  "The `ex-data` of the ex-info a thunk throws, or nil when it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- conviction
  "The conviction `assert` holds the rule `form` inert under in CxUniverse
  (`tu/write-conviction`), or nil for a rule stored and believed."
  [kb form]
  (tu/write-conviction kb form 'CxUniverse))

(defn- disjoint-pair
  "Two types the KB has been told share no instance, plus a third unrelated to both.
  Returns `[a b c]`."
  [kb]
  (let [a (tu/tmp-type) b (tu/tmp-type) c (tu/tmp-type)]
    (doseq [t [a b c]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (v/assert kb (list 'disjoint a b) 'CxUniverse)
    [a b c]))

(defn- permutations
  [coll]
  (if (< (count coll) 2)
    (list coll)
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

;; ---- two instance constraints on one variable ---------------------------

(tu/deftest-kb a-variable-two-arg-constraints-separate-is-held-inert
  (let [[a b] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred)
        form (list 'implies (list p '?x) (list q '?x))]
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 b) 'CxUniverse)
    (testing "check reports nothing, since assert stores the rule"
      (is (= [] (v/check kb form 'CxUniverse))))
    (let [h (v/assert kb form 'CxUniverse)]
      (testing "the antecedent binds ?x an a, the consequent places it where a b belongs"
        (is (integer? h))
        (is (not (v/in? kb h)))
        (let [c (:conviction (v/why-not kb h))]
          (is (= :arg-variable (:type c)))
          (is (= '?x (:variable c)))
          (is (= #{a b} (set (:expected c))))))
      (testing "violations names the rule"
        (is (= [[:inert-rule :arg-variable]]
               (keep #(when (= h (v/handle-of kb (:sentence %) (:context %)))
                        [(:violation %) (:type (:detail %))])
                     (v/violations kb)))))
      (testing "a recover holds it again"
        (v/recover kb)
        (is (not (v/in? kb h)))
        (is (= :arg-variable (:type (:conviction (v/why-not kb h))))))
      (v/retract! kb h))
    (testing "try-assert refuses it"
      (let [d (refusal #(v/try-assert kb form 'CxUniverse))]
        (is (= [:definitional-clash :arg-variable] [(:type d) (:violation d)]))
        (is (nil? (v/handle-of kb form 'CxUniverse)))))))

(tu/deftest-kb a-rule-a-separation-convicts-is-held-in-every-arrival-order
  ;; all 24 orders of {arg p, arg q, disjoint, rule}: the stored set, the rule's belief
  ;; and the report are the same in every one
  (let [outcomes (vec (for [order (permutations [:arg-p :arg-q :disjoint :rule])]
                        (tu/with-terms [p q a_ b_]
                          (v/assert kb (list 'genl a_ 'thing) 'CxUniverse)
                          (v/assert kb (list 'genl b_ 'thing) 'CxUniverse)
                          (let [form  (list 'implies (list p '?x) (list q '?x))
                                write {:arg-p    (list 'arg p 1 a_)
                                       :arg-q    (list 'arg q 1 b_)
                                       :disjoint (list 'disjoint a_ b_)
                                       :rule     form}]
                            (doseq [k order] (v/assert kb (write k) 'CxUniverse))
                            (let [h (v/handle-of kb form 'CxUniverse)
                                  c (:conviction (v/why-not kb h))
                                  r [(every? #(v/handle-of kb (write %) 'CxUniverse) (keys write))
                                     (v/in? kb h) (:type c) (:variable c) (set (:expected c))
                                     (some #(= h (v/handle-of kb (:sentence %) (:context %)))
                                           (filter #(= :inert-rule (:violation %)) (v/violations kb)))]]
                              (v/retract! kb h)
                              (mapv #(if (set? %) (count %) %) r))))))]
    (is (= 24 (count outcomes)))
    (is (= [[true false :arg-variable '?x 2 true]] (distinct outcomes)))))

(tu/deftest-kb a-genl-edge-under-the-separation-frees-and-convicts-a-held-rule
  ;; ?x is a c_ and a b_; c_ is separated from b_ only through `(genl c_ a_)`, below the
  ;; `disjoint` the conviction reads, so the edge leaving frees the rule and the edge
  ;; arriving holds it again
  (tu/with-terms [p q a_ b_ c_]
    (let [edge (list 'genl c_ a_)
          form (list 'implies (list p '?x) (list q '?x))
          _    (mapv #(v/assert kb % 'CxUniverse)
                     [(list 'genl a_ 'thing) (list 'genl b_ 'thing) (list 'genl c_ 'thing) edge
                      (list 'disjoint a_ b_) (list 'arg p 1 c_) (list 'arg q 1 b_) form])
          h    (v/handle-of kb form 'CxUniverse)
          in?  #(v/in? kb h)
          r    [(in?)
                (do (v/retract! kb (v/handle-of kb edge 'CxUniverse)) (in?))
                (do (v/assert kb edge 'CxUniverse) (in?))]]
      (is (= [false true false] r) "held, freed by the edge leaving, held by it arriving"))))

(tu/deftest-kb a-separation-leaving-fires-the-rule-it-released-at-that-write-in-either-order
  ;; the settle's argument-hold refresh releases the rule after the pass read its touched
  ;; set, so the rule is re-chained from the handles the refresh released
  (doseq [facts-first? [true false]]
    (tu/with-terms [p q a_ b_ Foo]
      (let [sep  (list 'disjoint a_ b_)
            rule (list 'set/forwardRule (list 'implies (list p '?x) (list q '?x)))
            _    (run! #(v/assert kb % 'CxUniverse)
                       [(list 'genl a_ 'thing) (list 'genl b_ 'thing) sep
                        (list 'arg p 1 a_) (list 'arg q 1 b_) rule])
            h    (v/handle-of kb rule 'CxUniverse)
            fact #(v/assert kb (list p Foo) 'CxUniverse)
            free #(v/retract! kb (v/handle-of kb sep 'CxUniverse))]
        (is (not (v/in? kb h)))
        (if facts-first? (do (fact) (free)) (do (free) (fact)))
        (let [c (v/handle-of kb (list q Foo) 'CxUniverse)]
          (is (= [true true true] [(v/in? kb h) (some? c) (boolean (and c (v/in? kb c)))])
              (if facts-first? "the fact before the release" "the release before the fact")))))))

(tu/deftest-kb try-assert-refuses-the-rule-and-the-declaration-in-either-order
  (testing "declarations first: the rule is refused"
    (tu/with-terms [p q a_ b_]
      (doseq [s [(list 'genl a_ 'thing) (list 'genl b_ 'thing) (list 'disjoint a_ b_)
                 (list 'arg p 1 a_) (list 'arg q 1 b_)]]
        (v/assert kb s 'CxUniverse))
      (let [form (list 'implies (list p '?x) (list q '?x))]
        (is (= :arg-variable (:violation (refusal #(v/try-assert kb form 'CxUniverse)))))
        (is (nil? (v/handle-of kb form 'CxUniverse))))))
  (testing "the rule first: the declaration that convicts it is refused, naming the rule"
    (tu/with-terms [p q a_ b_]
      (doseq [s [(list 'genl a_ 'thing) (list 'genl b_ 'thing) (list 'disjoint a_ b_)
                 (list 'arg p 1 a_)]]
        (v/assert kb s 'CxUniverse))
      (let [form (list 'implies (list p '?x) (list q '?x))
            h    (v/assert kb form 'CxUniverse)
            d    (refusal #(v/try-assert kb (list 'arg q 1 b_) 'CxUniverse))]
        (is (v/in? kb h))
        (is (= [:definitional-clash :arg-variable] [(:type d) (:violation d)]))
        (is (= [h] (mapv :handle (:clashes-with d))))
        (is (nil? (v/handle-of kb (list 'arg q 1 b_) 'CxUniverse)))
        (is (v/in? kb h) "nothing was stored, so the rule stays believed")
        (v/retract! kb h)))))

(tu/deftest-kb try-assert-refuses-a-covering-declaration-that-convicts-a-stored-rule
  (doseq [decl [(fn [q b_] (list 'argAndRest q 1 b_)) (fn [q b_] (list 'args q b_))]]
    (tu/with-terms [p q a_ b_]
      (doseq [s [(list 'genl a_ 'thing) (list 'genl b_ 'thing) (list 'disjoint a_ b_)
                 (list 'arg p 1 a_)]]
        (v/assert kb s 'CxUniverse))
      (let [h (v/assert kb (list 'implies (list p '?x) (list q '?x)) 'CxUniverse)
            d (decl q b_)
            r (refusal #(v/try-assert kb d 'CxUniverse))]
        (is (= [:definitional-clash :arg-variable [h]]
               [(:type r) (:violation r) (mapv :handle (:clashes-with r))])
            (pr-str d))
        (is (nil? (v/handle-of kb d 'CxUniverse)))
        (is (v/in? kb h))
        (v/retract! kb h)))))

(tu/deftest-kb args-and-arg-at-position-1-judge-a-rule-alike
  (let [verdict (fn [decl]
                  (tu/with-terms [p q a_ b_]
                    (doseq [s [(list 'genl a_ 'thing) (list 'genl b_ 'thing) (list 'disjoint a_ b_)
                               (list 'arg p 1 a_) (decl q b_)]]
                      (v/assert kb s 'CxUniverse))
                    (:type (conviction kb (list 'implies (list p '?x) (list q '?x))))))]
    (is (= [:arg-variable :arg-variable]
           [(verdict #(list 'arg %1 1 %2)) (verdict #(list 'args %1 %2))]))))

(tu/deftest-kb a-believed-rule-goes-out-with-its-conclusions-when-a-declaration-convicts-it
  (tu/with-terms [p q a_ b_ Foo]
    (doseq [s [(list 'genl a_ 'thing) (list 'genl b_ 'thing) (list 'disjoint a_ b_)
               (list 'arg p 1 a_)]]
      (v/assert kb s 'CxUniverse))
    (let [h   (v/assert kb (list 'set/forwardRule (list 'implies (list p '?x) (list q '?x)))
                        'CxUniverse)
          _   (v/assert kb (list p Foo) 'CxUniverse)
          qf  #(v/handle-of kb (list q Foo) 'CxUniverse)]
      (is (and (qf) (v/in? kb (qf))) "the rule fires while nothing convicts it")
      (let [d (v/assert kb (list 'arg q 1 b_) 'CxUniverse)]
        (is (not (v/in? kb h)))
        (is (not (and (qf) (v/in? kb (qf)))) "its conclusion has no support left")
        (testing "and retracting the declaration releases both"
          (v/retract! kb d)
          (is (v/in? kb h))
          (is (and (qf) (v/in? kb (qf))))))
      (v/retract! kb h))))

(tu/deftest-kb a-variable-two-compatible-arg-constraints-stands
  (let [[a _ c] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred)]
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 c) 'CxUniverse)
    (testing "nothing separates the two types, so the rule is believed"
      (is (nil? (conviction kb (list 'implies (list p '?x) (list q '?x))))))))

(tu/deftest-kb the-clash-is-found-inside-one-literal-too
  (let [[a b] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred)]
    (v/assert kb (list 'arity q 2) 'CxUniverse)
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 2 b) 'CxUniverse)
    (testing "one variable in both positions of a literal is still one term"
      (is (= :arg-variable
             (:type (conviction kb (list 'implies (list p '?x) (list q '?x '?x)))))))))

(tu/deftest-kb a-negated-antecedent-constrains-nothing
  (let [[a b] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred) r (tu/tmp-pred)]
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 b) 'CxUniverse)
    (v/assert kb (list 'arg r 1 a) 'CxUniverse)
    (testing "`(not (q ?x))` says ?x is not a b — which is what its author meant"
      (is (nil? (conviction kb (list 'implies (list 'and (list p '?x) (list 'not (list q '?x)))
                                     (list r '?x))))))))

(tu/deftest-kb the-constraint-descends-the-predicate-hierarchy
  (let [[a b] (disjoint-pair kb)
        p (tu/tmp-pred) q (tu/tmp-pred) sub (tu/tmp-pred)]
    (v/assert kb (list 'arg p 1 a) 'CxUniverse)
    (v/assert kb (list 'arg q 1 b) 'CxUniverse)
    (v/assert kb (list 'genl sub q) 'CxUniverse)
    (testing "a super-predicate's declaration binds the sub-predicate's tuples here too"
      (let [c (conviction kb (list 'implies (list p '?x) (list sub '?x)))]
        (is (= :arg-variable (:type c)))
        (is (re-find (re-pattern (str "declared of " q)) (:message c)))))))

;; ---- the type-level half ------------------------------------------------

(tu/deftest-kb a-genlArg-position-asks-for-a-type
  (let [text (tu/tmp-type)
        p (tu/tmp-pred) rel (tu/tmp-pred)]
    (v/assert kb (list 'genl text 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint text 'unary_predicate) 'CxUniverse)
    (v/assert kb (list 'arg p 1 text) 'CxUniverse)
    (v/assert kb (list 'type_relation_predicate rel) 'CxUniverse)
    (v/assert kb (list 'genlArg rel 1 'thing) 'CxUniverse)
    (testing "a variable bound to a text is not a kind, so it cannot fill a kind slot"
      (is (= :arg-variable
             (:type (conviction kb (list 'implies (list p '?x) (list rel '?x)))))))))

(tu/deftest-kb a-typeRelationPredicate-constrains-a-position-no-declaration-names
  (let [text (tu/tmp-type)
        p (tu/tmp-pred) rel (tu/tmp-pred) t (tu/tmp-type)]
    (v/assert kb (list 'genl text 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint text 'predicate) 'CxUniverse)
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'arg p 1 text) 'CxUniverse)
    (v/assert kb (list 'genlArg rel 1 'thing) 'CxUniverse)   ; position 1 only
    (let [form (list 'implies (list p '?x) (list rel t '?x))
          h    (v/assert kb form 'CxUniverse)]
      (is (v/in? kb h) "nothing types position 2 yet")
      (testing "the relation kind, arriving after the rule, says of position 2 what no genlArg was written for"
        (v/assert kb (list 'type_relation_predicate rel) 'CxUniverse)
        (is (not (v/in? kb h)))
        (is (re-find #"type_relation_predicate" (:message (:conviction (v/why-not kb h))))))
      (v/retract! kb h))))

(tu/deftest-kb a-genl-over-a-binary-predicate-class-is-not-an-inert-rule
  ;; #244: a type_relation_predicate's positions ask for what its `args` declaration
  ;; names, `predicate` from core.txt's forward rule, so a class of binary predicates
  ;; fills genl's first argument; the rule written before its declarations and after
  (let [outcomes (vec (for [rule-first? [true false]]
                        (tu/with-terms [pair_type pair_kind steady_kind targetRel]
                          (let [form  (list 'implies (list 'and (list pair_kind '?r) (list 'genl '?r targetRel))
                                            (list steady_kind '?r))
                                decls [(list 'genl pair_type 'predicate) (list 'disjoint pair_type 'unary_predicate)
                                       (list 'genl pair_kind 'thing) (list 'genl steady_kind 'thing)
                                       (list 'arg pair_kind 1 pair_type)]
                                _     (run! #(v/assert kb % 'CxUniverse)
                                            (if rule-first? (cons form decls) (concat decls [form])))
                                h     (v/handle-of kb form 'CxUniverse)
                                inert #(some (fn [v] (and (= :inert-rule (:violation v))
                                                          (= h (v/handle-of kb (:sentence v) (:context v)))))
                                             (v/violations kb))
                                live  [(some? h) (v/in? kb h) (boolean (inert))]]
                            (v/recover kb)
                            (let [r [live [(v/in? kb h) (boolean (inert))]]]
                              (v/retract! kb h)
                              r)))))]
    (is (= [[[true true false] [true false]]] (distinct outcomes)))))

(tu/deftest-kb a-rule-over-genl-fires-on-the-shipped-edge-between-binary-predicates
  ;; abstract.txt's (genl performedBy doneBy) places one binary predicate under another
  (tu/with-terms [doerMark Tag]
    (v/assert kb (list 'arg doerMark 1 'binary_predicate) 'CxUniverse)
    (let [rule (list 'set/forwardRule (list 'implies (list 'genl '?r 'doneBy) (list doerMark '?r Tag)))
          h    (v/assert kb rule 'CxUniverse)
          c    (v/handle-of kb (list doerMark 'performedBy Tag) 'CxUniverse)]
      (is (= [true true] [(v/in? kb h) (boolean (and c (v/in? kb c)))]))
      (v/retract! kb h))))

;; ---- the two forms the issue named --------------------------------------

(tu/deftest-kb the-shipped-schema-holds-a-string-fed-into-a-type-slot
  (testing "?kind is asked for a kind at both ends — believed"
    (is (nil? (conviction kb '(implies (arg ?pred ?n ?kind) (genl ?pred ?kind))))))
  (testing "?string is a string in the antecedent and a kind in the consequent"
    (let [c (conviction kb '(implies (comment ?x ?string) (genl ?x ?string)))]
      (is (= :arg-variable (:type c)))
      (is (= '?string (:variable c)))
      (is (= '[string predicate] (:expected c))))))

(tu/deftest-kb the-shipped-schema-holds-a-function-fed-into-a-type-slot
  ;; The second half of CxUniverse's "A function is a relation, and is not a predicate", as a
  ;; fact rather than as prose — derived from the partition of `relation`, not stated.  Every type is a unary_predicate,
  ;; so a type-level position asks for a predicate, and the three declarations that
  ;; name a function-valued argument all meet `genl` on a variable no term can fill.
  (doseq [pred '[result genlResult functionCorrespondingPredicate]]
    (testing (str pred " arg 1 is a function, and genl arg 1 is a type")
      (let [form (list 'implies (if (= pred 'functionCorrespondingPredicate)
                                  (list pred '?f '?p 2)
                                  (list pred '?f '?t))
                       (list 'genl '?f (if (= pred 'functionCorrespondingPredicate) '?p '?t)))
            c    (conviction kb form)]
        (is (= :arg-variable (:type c)))
        (is (= '?f (:variable c)))
        (is (= '[function predicate] (:expected c))))))
  (testing "and the type-valued position of the same literal is unaffected"
    (is (nil? (conviction kb '(implies (result ?f ?t) (genl ?t ?t)))))))

(tu/deftest-kb the-value-kinds-are-one-vocabulary-and-a-symbol-is-held-out-of-a-type-slot
  (testing "the disjointness on number carries integer with it"
    ;; `(arg arity 2 non_negative_integer)`, and that type is below integer and number,
    ;; which no relation is
    (let [c (conviction kb '(implies (arity ?p ?n) (genl ?p ?n)))]
      (is (= :arg-variable (:type c)))
      (is (= '?n (:variable c)))
      (is (= '[non_negative_integer predicate] (:expected c)))))
  (testing "a symbol fed into a type slot is held, mention and use being disjoint"
    ;; symbol reaches expression through atomic_term and atomic_expression, and
    ;; expression is disjoint from relation, so a variable asked for a symbol at one end
    ;; and a kind at the other has nothing left that can fill it
    (let [p (tu/tmp-pred)]
      (v/assert kb (list 'arg p 1 'symbol) 'CxUniverse)
      (let [c (conviction kb (list 'implies (list p '?x) (list 'genl '?x 'thing)))]
        (is (= :arg-variable (:type c)))
        (is (= '?x (:variable c)))
        (is (= '[symbol predicate] (:expected c)))))))

;; ---- the other entry point: a rule nobody typed ---------------------------------
;; A mint reads `check-rule!` as a **value** (`checks/rule-violation`) and drops what it
;; refuses, because an exception escaping a firing would leave the fixpoint half
;; computed.  The `:arg-variable` arm refuses nothing there: a convicted mint is stored
;; and held inert, as an asserted rule is.  Both mint entry points are here: a
;; generator's fill, and a `defn*` fact's companion rule.

(defn- mentioning
  "The stored rules in `ctx` whose sentence names `term` anywhere."
  [kb ctx term]
  (filter #(and (:antecedent %)
                (some #{term} (tree-seq sequential? seq (v/sentence-of %))))
          (v/sentexes-in-context kb ctx)))

(tu/deftest-kb a-generator-mint-that-clashes-is-held-inert-in-either-order
  (doseq [decls-first? [true false]]
    (testing (if decls-first? "declarations before the fill" "the fill before the declarations")
      (let [[a b] (disjoint-pair kb)
            marker (tu/tmp-pred) src (tu/tmp-pred) fine (tu/tmp-pred) dst (tu/tmp-pred)
            decls  [(list 'arg src 1 a) (list 'arg fine 1 b) (list 'arg dst 1 b)]
            fills  [(list marker fine) (list marker src)]]
        ;; the generator itself carries no clash: `?p` is a hole, so the antecedent it
        ;; heads declares nothing until a firing grounds it
        (v/assert kb (list 'implies (list marker '?p)
                           (list 'implies (list '?p '?x) (list dst '?x)))
                  'CxUniverse)
        (doseq [s (if decls-first? (concat decls fills) (concat fills decls))]
          (v/assert kb s 'CxUniverse))
        (let [minted (fn [t] (first (mentioning kb 'CxUniverse t)))]
          (is (v/in? kb (:id (minted fine))) "a fill whose declaration agrees generates a believed rule")
          (is (some? (minted src)) "a fill whose declaration contradicts it is stored")
          (is (not (v/in? kb (:id (minted src)))))
          (let [c (:conviction (v/why-not kb (:id (minted src))))]
            (is (= :arg-variable (:type c)))
            (is (= #{a b} (set (:expected c))))))))))

(tu/deftest-kb a-defn-companion-rule-that-clashes-is-held-inert
  ;; the second mint entry point: `defnSufficient` names a membership at both ends, so the two
  ;; argument declarations meet on the `?x` the companion rule carries between them
  (let [[a b] (disjoint-pair kb)
        coll (tu/tmp-pred) cond' (tu/tmp-pred)]
    (v/assert kb (list 'arg cond' 1 a) 'CxUniverse)
    (v/assert kb (list 'arg coll 1 b) 'CxUniverse)
    (v/assert kb (list 'defnSufficient coll (list cond' '?x)) 'CxUniverse)
    (let [r (first (mentioning kb 'CxUniverse cond'))]
      (is (some? r) "the companion rule is stored")
      (is (not (v/in? kb (:id r))))
      (is (= :arg-variable (:type (:conviction (v/why-not kb (:id r)))))))))

;; ---- quotedArg: a self-denoting kind convicts, any other kind does not ----------
;; A quoted demand at `string` or `number` asks for a literal, which is an instance of its
;; kind.  A quoted demand at any other kind, and a pair of two quoted demands, are not
;; judged: where no term satisfies both ends the rule is stored and believed
;; (docs/argtypes.md).

(tu/deftest-kb a-quoted-string-demand-and-a-separated-instance-demand-hold-the-rule
  (let [qs (tu/tmp-pred) ap (tu/tmp-pred)]
    (v/assert kb (list 'unary_predicate qs) 'CxUniverse)
    (v/assert kb (list 'quotedArg qs 1 'string) 'CxUniverse)
    (v/assert kb (list 'unary_predicate ap) 'CxUniverse)
    (v/assert kb (list 'arg ap 1 'predicate) 'CxUniverse)
    (let [c (conviction kb (list 'implies (list qs '?x) (list ap '?x)))]
      (is (= :arg-variable (:type c)))
      (is (= '[string predicate] (:expected c)))
      (is (re-find #"a string literal \(arg 1 of" (:message c))))))

(tu/deftest-kb a-quoted-string-demand-and-a-type-level-position-hold-the-rule
  (let [qs (tu/tmp-pred)]
    (v/assert kb (list 'unary_predicate qs) 'CxUniverse)
    (v/assert kb (list 'quotedArg qs 1 'string) 'CxUniverse)
    (is (= '[string predicate]
           (:expected (conviction kb (list 'implies (list qs '?x) (list 'genl '?x 'thing))))))))

(tu/deftest-kb a-quoted-symbol-demand-is-not-judged-by-the-rule-arm
  ;; a symbol expression denotes the term the other end types
  (let [qs (tu/tmp-pred) ap (tu/tmp-pred)]
    (v/assert kb (list 'unary_predicate qs) 'CxUniverse)
    (v/assert kb (list 'quotedArg qs 1 'symbol) 'CxUniverse)
    (v/assert kb (list 'unary_predicate ap) 'CxUniverse)
    (v/assert kb (list 'arg ap 1 'predicate) 'CxUniverse)
    (is (nil? (conviction kb (list 'implies (list qs '?x) (list ap '?x)))))
    (is (nil? (conviction kb (list 'implies (list qs '?x) (list 'genl '?x 'thing)))))))

(tu/deftest-kb two-quoted-demands-are-not-judged-by-the-rule-arm
  ;; no literal is both a string and an integer
  (let [qs (tu/tmp-pred) qi (tu/tmp-pred) f (tu/tmp-ind)]
    (v/assert kb (list 'unary_predicate qs) 'CxUniverse)
    (v/assert kb (list 'quotedArg qs 1 'string) 'CxUniverse)
    (v/assert kb (list 'unary_predicate qi) 'CxUniverse)
    (v/assert kb (list 'quotedArg qi 1 'integer) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (is (nil? (conviction kb (list 'implies (list qs '?x) (list qi '?x)))))
    (testing "a compound is held under either demand"
      (is (= :quoted-arg-type (:type (tu/write-conviction kb (list qs (list f 5)) 'CxUniverse))))
      (is (= :quoted-arg-type (:type (tu/write-conviction kb (list qi (list f 5)) 'CxUniverse)))))))

;; ---- the kinds the arm does not read, and why ----------------------------------
;; Every test here is a **witness for an absence**: it goes red the moment somebody
;; widens the arm.  `interArg` has a binding both ends accept, so convicting the rule would
;; hold one that works.

(tu/deftest-kb an-interArg-trigger-is-a-demand-not-a-fact
  ;; the decisive one, and the reason `interArg` cannot join the arm at all: `(arg P i
  ;; T)` does not make argument i a T — an unclassified term satisfies it vacuously — so
  ;; no rule's own bindings entail the trigger, and a conditional constraint that never
  ;; provably fires can convict nothing.
  (let [[u v'] (disjoint-pair kb)
        a      (tu/tmp-type)
        ia     (tu/tmp-pred) trig (tu/tmp-pred) tgt (tu/tmp-pred)
        Unc    (tu/tmp-ind)  Val  (tu/tmp-ind)]
    (v/assert kb (list 'genl a 'thing) 'CxUniverse)
    (v/assert kb (list 'binary_predicate ia) 'CxUniverse)
    (v/assert kb (list 'interArg ia 1 a 2 u) 'CxUniverse)
    (v/assert kb (list 'unary_predicate trig) 'CxUniverse)
    (v/assert kb (list 'arg trig 1 a) 'CxUniverse)
    (v/assert kb (list 'binary_predicate tgt) 'CxUniverse)
    (v/assert kb (list 'arg tgt 2 v') 'CxUniverse)
    (testing "the rule is believed, though the interArg target and the arg type are disjoint"
      (is (nil? (conviction kb (list 'implies (list 'and (list trig '?x) (list ia '?x '?y))
                                     (list tgt '?x '?y))))))
    (testing "and a binding that classifies neither variable satisfies the whole chain"
      (is (= [] (v/check kb (list trig Unc) 'CxUniverse)))
      (is (= [] (v/check kb (list ia Unc Val) 'CxUniverse)))
      (is (= [] (v/check kb (list tgt Unc Val) 'CxUniverse))))))

(tu/deftest-kb an-instance-demand-and-a-subtype-demand-are-not-a-clash
  ;; beyond the `unary_predicate` mapping the arm already makes: a term may be an instance
  ;; of one type and a subtype of another at once, and the meta-ontology depends on it —
  ;; every type in the KB is an instance of unary_predicate.
  (let [d (tu/tmp-type) inst (tu/tmp-pred) sub (tu/tmp-pred) both (tu/tmp-type)]
    (v/assert kb (list 'genl d 'thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate inst) 'CxUniverse)
    (v/assert kb (list 'arg inst 1 d) 'CxUniverse)
    (v/assert kb (list 'binary_predicate sub) 'CxUniverse)
    (v/assert kb (list 'genlArg sub 1 'thing) 'CxUniverse)
    (is (nil? (conviction kb (list 'implies (list inst '?x) (list sub '?x 'thing)))))
    (testing "one term, both readings"
      (v/assert kb (list d both) 'CxUniverse)
      (v/assert kb (list 'genl both 'thing) 'CxUniverse)
      (is (= [] (v/check kb (list sub both 'thing) 'CxUniverse))))))

(tu/deftest-kb a-variable-functor-carries-no-argument-constraints
  ;; `?pred` names no predicate, so nothing declares its positions.  Reading it as one
  ;; hands `declaration-reader` a match pattern instead of a name and EVERY (arg P n T)
  ;; in the KB comes back, so a variadic rule collects two unrelated predicates' demands
  ;; on one variable — (arg typeToInstancePred 2 instance_relation_predicate) beside
  ;; (arg instantNotEqual 2 time_point) — and is convicted of a clash neither declaration
  ;; is about.
  (testing "an inert variadic rule is believed"
    (is (nil? (conviction kb '(set/inertRule
                               (implies (?pred . ?args) (holdsIn CxUniverse (?pred . ?args))))))))
  (testing "a bare variadic rule keeps its OWN refusal"
    (is (some #(= :not-indexable (:type %))
              (v/check kb '(implies (?pred ?a ?b) (?pred ?b ?a)) 'CxUniverse))))
  (testing "while a CONCRETE functor still convicts a variable its own positions clash on"
    (tu/with-terms [narrowOf lithe_thing squat_thing A]
      (v/assert kb (list 'genl lithe_thing 'thing) 'CxUniverse)
      (v/assert kb (list 'genl squat_thing 'thing) 'CxUniverse)
      (v/assert kb (list 'disjoint lithe_thing squat_thing) 'CxUniverse)
      (v/assert kb (list 'binary_predicate narrowOf) 'CxUniverse)
      (v/assert kb (list 'arg narrowOf 1 lithe_thing) 'CxUniverse)
      (v/assert kb (list 'arg narrowOf 2 squat_thing) 'CxUniverse)
      (is (= :arg-variable
             (:type (conviction kb (list 'implies (list narrowOf '?x '?x) (list 'thing A)))))
          "a real predicate's own two disjoint positions still convict one variable"))))
