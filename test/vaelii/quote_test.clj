;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quote-test
  "Mention opacity for the quoting functions (`Quote`, `Quasiquote`) — docs/nat.md,
  docs/equality.md.

  A `Quote` reified NAT names a term *as syntax*: `(cycl_constant (Quote Muffet))` reifies
  to `(cycl_constant K)`, an ordinary unary type membership on an opaque constant, reusing
  the NAT machinery.  Being a quoting function — fixed by the engine, never declared — adds
  opacity in the equality congruence: a `rewriteOf` **spelling** rename reaches into the
  mention, but a `sameAs` / `equals` **identity** merge of the referent does not fold the
  quoted term."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu]))

;; The fixture loads the upper layer, whose reflection.txt holds the expression lattice the
;; shape classification answers in.
(use-fixtures :once (tu/loaded #(doto %
                                  (tu/load-core!))))
(use-fixtures :each (tu/neutral))

(def ^:private Quote
  "The engine's `Quote`, a quoting function fixed by the engine — a stand-in term would
  quote nothing."
  sx/quote-functor)

(def ^:private Quasiquote
  "The engine's `Quasiquote`, the other quoting function."
  sx/quasiquote-functor)

(defn- declare-quote!
  "Declare `Quote` reifiable, its reified constants `cycl_expression` instances by default,
  with `cycl_constant` a subtype.  It quotes without any declaration."
  [kb Quote cycl_expression cycl_constant]
  (v/assert kb (list 'genl cycl_expression 'thing)        'CxUniverse)
  (v/assert kb (list 'genl cycl_constant cycl_expression) 'CxUniverse)
  (v/assert kb (list 'reifiable_function Quote)            'CxUniverse)
  (v/assert kb (list 'result Quote cycl_expression)    'CxUniverse))

(defn- k-of [kb h] (second (:sentence (v/sentex kb h))))

(tu/deftest-kb a-quoted-term-reifies-and-is-typed-as-syntax
  (tu/with-terms [Muffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [h (v/assert kb (list cycl_constant (list Quote Muffet)) 'CxUniverse)
          k (k-of kb h)]
      (is (nat-read/reified-nat-symbol? k) "the quoted term reifies to an opaque constant")
      (is (= (list Quote Muffet) (nat/nat-expression kb k)))
      (is (v/isa? kb k cycl_constant 'CxUniverse)   "K is a cycl_constant")
      (is (v/isa? kb k cycl_expression 'CxUniverse) "and a cycl_expression up the genl"))))

;; ---- use versus mention: what a sentex denotes, not what it mentions ------
;; `dog` written in a sentence denotes the predicate `dog`: use is the default.  Only
;; `(Quote dog)` mentions `dog`, denoting the symbol `dog`.  symbol is below expression,
;; and expression is disjoint from relation, so no term is both a symbol and a predicate.

(tu/deftest-kb a-symbol-is-a-mention-and-no-predicate
  (tu/with-terms [dog holds]
    (v/assert kb (list 'reifiable_function Quote) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog)      'CxUniverse)
    (v/assert kb (list 'unary_predicate holds)    'CxUniverse)
    (v/assert kb (list holds (list Quote dog))    'CxUniverse)   ; mints (Quote dog) -> K
    (testing "dog written plainly denotes the predicate dog"
      (is (v/ask? kb (list 'predicate dog) 'CxUniverse)))
    (testing "dog written plainly is not itself a symbol"
      (is (not (v/ask? kb (list 'symbol dog) 'CxUniverse))))
    (testing "symbol and predicate share no instance"
      (is (v/disjoint? kb 'symbol 'predicate)))))

;; ---- shape classification: what (Quote X) IS follows from X, not a declaration -----
;; CxUniverse's `Quote` comment says Quote takes no result, arg or metatype declaration: what
;; kind of expression `(Quote X)` is follows from X's shape (`provers/shape-kinds`).
;; `Quote` is unreifiable here, so a ground quoted form reaches the prover as written; a
;; reifiable one is read back through its constant's `natFormula` (the next test).
(tu/deftest-kb quoted-forms-are-classified-by-shape
  (tu/with-terms [dog]
    (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog)         'CxUniverse)
    (doseq [[kind x holds? why]
            [['symbol dog true "dog's shape being an atomic_term"]
             ['number 212 true "212's shape being an unrepresented_term"]
             ['integer 5 true "a quoted integer is an integer, a value denoting itself"]
             ['non_atomic_expression (list dog 'Muffet) true "(dog Muffet)'s shape being one"]
             ['symbol (list dog 'Muffet) false "a compound's shape is not atomic"]
             ;; the expression ?x is open, reflection.txt's variable being an
             ;; open_expression; the sentence around (Quote ?x) is closed (`sx/closed?`)
             ['variable '?x true "?x is a variable"]
             ['wff_expression '?x true "an atomic_expression is a wff_expression"]
             ['open_expression '?x true "?x is free in the quoted form"]
             ['closed_expression '?x false "an expression is open or closed, not both"]
             ['open_formula (list 'implies (list 'poodle '?x) (list dog '?x)) true
              "?x is free in the quoted form"]
             ['sentence (list 'forall '?x (list 'implies (list dog '?x) (list 'animal '?x))) true
              "a quantifier binds its variable"]
             ['sentence (list 'forAll 'Muffet (list dog 'Muffet)) false
              "forAll is a predicate's spelling, and forall is the quantifier"]
             ['ill_formed_expression (list 3 4) true "a number in operator position"]
             ['sentex_handle_term (list 'sentexHandle 212) true "a handle names a stored sentex"]
             ['closed_expression (list 'sentexHandle 212) true "a handle is a closed non_atomic_term"]
             ['sentex_handle_term 212 false "a bare integer names no sentex"]
             ['sentex_handle_term (list 'sentexHandle 0) false "a handle's id is a positive integer"]
             ['sentex_handle_term (list 'sentexHandle "212") false "and an integer"]
             ['sentex_handle_term (list 'sentexHandle 212 213) false "a handle names one sentex"]]]
      (testing (str (list kind (list 'Quote x)) " " holds? ": " why)
        (is (= holds? (v/ask? kb (list kind (list Quote x)) 'CxUniverse)))))))

(tu/deftest-kb a-reified-quoted-form-is-classified-through-its-nat-formula
  (tu/with-terms [dog cycl_expression cycl_constant said Tom]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (let [h (v/assert kb (list said Tom (list Quote (list 'not (list dog 'Muffet)))) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat-read/reified-nat-symbol? k) "the quoted form is minted")
      (is (v/ask? kb (list 'sentence (list Quote (list 'not (list dog 'Muffet)))) 'CxUniverse)
          "the quoted spelling reads back to its constant")
      (is (v/ask? kb (list 'sentence k) 'CxUniverse) "and so does the constant")
      (is (not (v/ask? kb (list 'symbol k) 'CxUniverse))
          "a formula's shape is not atomic"))))

(tu/deftest-kb a-firing-over-a-quoted-form-needs-no-quoting-declaration
  ;; `ExpressionKindProver` is a SupportingProver: `Quote` is a quoting function with no
  ;; statement behind it, so the firing over a quoted form rests on the fact it read and
  ;; the `genl` path from the form's shape kind, and withdrawing the fact withdraws the
  ;; conclusion.  A `not` head makes the quoted form a sentence by its spelling alone, and
  ;; `formula` is one `genl` edge above `sentence`.
  (tu/with-terms [dog said asserter Tom]
    (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list said '?a '?q) (list 'formula '?q))
                       (list asserter '?a))
              'CxUniverse {:direction :forward})
    (let [m (v/assert kb (list said Tom (list Quote (list 'not (list dog 'Muffet)))) 'CxUniverse)]
      (is (v/ask? kb (list asserter Tom) 'CxUniverse) "the quoted form joins the rule")
      (v/retract! kb m)
      (is (not (v/ask? kb (list asserter Tom) 'CxUniverse))
          "and retracting the fact withdraws the conclusion"))))

;; ---- the head's stored kind: predication, non_atomic_term, ill-formed ---------------
;; Whether `(R a)` is a predication or a non_atomic_term, and whether R's length admits its
;; arguments, is what the KB states of R (`provers/stated-kinds`), never R's spelling.

(tu/deftest-kb a-quoted-application-is-classified-by-its-heads-stored-kind
  (tu/with-terms [dog MotherFn hound]
    (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
    (v/assert kb (list 'predicate dog) 'CxUniverse)
    (v/assert kb (list 'arity dog 1) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'arity MotherFn 1) 'CxUniverse)
    (doseq [[kind x holds? why]
            [['closed_predication (list dog 'Muffet) true "dog is a predicate"]
             ['literal (list dog 'Muffet) true "a predication is a literal"]
             ['sentence (list dog 'Muffet) true "a closed predication is a sentence"]
             ['open_predication (list dog '?x) true "?x is free in it"]
             ['sentence (list dog '?x) false "an open predication is no sentence"]
             ['non_atomic_term (list dog 'Muffet) false "dog is no function"]
             ['non_atomic_term (list MotherFn 'Muffet) true "MotherFn is a function"]
             ['wff_expression (list MotherFn 'Muffet) true "a denotational_term is a wff_expression"]
             ['predication (list MotherFn 'Muffet) false "MotherFn is no predicate"]
             ['non_atomic_term (list MotherFn '?x) false "a denotational_term is closed"]
             ['open_expression (list MotherFn '?x) true "its spelling decides openness"]
             ['predication (list hound 'Muffet) false "the KB states nothing of hound"]
             ['non_atomic_term (list hound 'Muffet) false "the KB states nothing of hound"]
             ['non_atomic_expression (list hound 'Muffet) true "its spelling decides that much"]
             ['ill_formed_sentence (list dog 'Muffet 'Rex) true "dog takes one argument"]
             ['predication (list dog 'Muffet 'Rex) false "an ill-formed expression predicates nothing"]
             ['ill_formed (list dog '?x 'Rex) true "an open application of a predicate is a formula"]
             ['ill_formed_expression (list MotherFn 'A 'B) true "MotherFn takes one argument"]
             ['non_atomic_term (list MotherFn 'A 'B) false "an ill-formed expression denotes nothing"]]]
      (testing (str (list kind (list 'Quote x)) " " holds? ": " why)
        (is (= holds? (v/ask? kb (list kind (list Quote x)) 'CxUniverse)))))))

;; The head's membership and its length are data on no functor a rule over a quoted form
;; names: `provers/support-answers-reading` re-joins the rule when a membership of a type
;; below `relation` arrives, and `special/recheck-on-lengths` when a settle moves a length.

(tu/deftest-kb a-predication-antecedent-fires-in-every-arrival-order-and-withdraws-with-the-kind
  (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
  (doseq [order (oi/permutations [:rule :fact :kind])]
    (tu/with-terms [dog said asserter Tom]
      (let [hs (into {} (for [o order]
                          [o (case o
                               :rule (v/assert kb (list 'implies (list 'and (list said '?a '?q) (list 'predication '?q))
                                                        (list asserter '?a))
                                               'CxUniverse {:direction :forward})
                               :fact (v/assert kb (list said Tom (list Quote (list dog 'Muffet))) 'CxUniverse)
                               :kind (v/assert kb (list 'predicate dog) 'CxUniverse))]))]
        (is (v/ask? kb (list asserter Tom) 'CxUniverse) (str (vec order) " fires"))
        (v/retract! kb (:kind hs))
        (is (not (v/ask? kb (list asserter Tom) 'CxUniverse)) (str (vec order) " withdraws"))))))

(tu/deftest-kb an-ill-formed-antecedent-fires-in-every-arrival-order-of-an-inherited-length
  (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
  (doseq [order (oi/permutations [:rule :fact :length :edge])]
    (tu/with-terms [dog animal said asserter Tom]
      (let [hs (into {} (for [o order]
                          [o (case o
                               :rule   (v/assert kb (list 'implies (list 'and (list said '?a '?q)
                                                                         (list 'ill_formed_expression '?q))
                                                          (list asserter '?a))
                                                 'CxUniverse {:direction :forward})
                               :fact   (v/assert kb (list said Tom (list Quote (list dog 'A 'B))) 'CxUniverse)
                               :length (v/assert kb (list 'arity animal 1) 'CxUniverse)
                               :edge   (v/assert kb (list 'genl dog animal) 'CxUniverse))]))]
        (is (v/ask? kb (list asserter Tom) 'CxUniverse) (str (vec order) " fires"))
        (v/retract! kb (:edge hs))
        (is (not (v/ask? kb (list asserter Tom) 'CxUniverse)) (str (vec order) " withdraws"))))))

(tu/deftest-kb a-length-arriving-withdraws-the-predication-it-breaks
  (tu/with-terms [dog said well_said ill_said Tom]
    (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
    (v/assert kb (list 'predicate dog) 'CxUniverse)
    (doseq [[k c] [['predication well_said] ['ill_formed ill_said]]]
      (v/assert kb (list 'implies (list 'and (list said '?a '?q) (list k '?q)) (list c '?a))
                'CxUniverse {:direction :forward}))
    (v/assert kb (list said Tom (list Quote (list dog 'A 'B))) 'CxUniverse)
    (let [read #(vector (v/ask? kb (list well_said Tom) 'CxUniverse)
                        (v/ask? kb (list ill_said Tom) 'CxUniverse))
          before (read)
          h      (v/assert kb (list 'arity dog 1) 'CxUniverse)
          during (read)]
      (v/retract! kb h)
      (is (= [[true false] [false true] [true false]] [before during (read)])
          "(dog A B) is a predication until dog's length is one"))))

(defn- believed-firings
  "`{conclusion #{[rule-sentence #{antecedent-sentence}]}}` for each believed `(c ?x)` of a
  functor in `cs`: the firing and its justifications by content, so two KB values over one
  store compare."
  [kb cs]
  (let [read #(some-> (v/sentex kb %) v/sentence-of)]
    (into {} (for [c cs
                   s (v/sentexes-matching kb (list c '?x) '?c)
                   :when (v/in? kb (:id s))]
               [(:sentence s)
                (into #{} (map (fn [j] [(read (:informant j)) (into #{} (map read) (:antecedents j))]))
                      (v/supporting-justifications kb (:id s)))]))))

(defn- restart-readings!
  "Assert, in each of `orders` and once per row, a forward rule over `(predication ?q)` and
  one over `(ill_formed ?q)`, a quoted `(dog A)` (row `:predication`) or, after `(arity dog
  1)`, `(dog A B)` (row `:ill-formed`), the membership `(my_kind dog)` and `(genl my_kind
  predicate)`.  Assert that each run fires its row's rule alone, and that the firing and its
  justifications read the same on a restart: a second KB value over the same store, its
  taxonomy and JTMS rebuilt by `recover` (recover_independence_test's `restarted`).  Every
  run is asserted before the one restart reads them all."
  [kb orders]
  (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
  (let [runs (doall
              (for [row [:predication :ill-formed]
                    order orders]
                (tu/with-terms [dog my_kind said well_said ill_said Tom]
                  (when (= :ill-formed row) (v/assert kb (list 'arity dog 1) 'CxUniverse))
                  (doseq [o order]
                    (case o
                      :rule (doseq [[k c] [['predication well_said] ['ill_formed ill_said]]]
                              (v/assert kb (list 'implies (list 'and (list said '?a '?q) (list k '?q)) (list c '?a))
                                        'CxUniverse {:direction :forward}))
                      :fact (v/assert kb (list said Tom (list Quote (if (= :ill-formed row)
                                                                      (list dog 'A 'B)
                                                                      (list dog 'A))))
                                      'CxUniverse)
                      :kind (v/assert kb (list my_kind dog) 'CxUniverse)
                      :edge (v/assert kb (list 'genl my_kind 'predicate) 'CxUniverse)))
                  {:row row :order order :fired (list (if (= :ill-formed row) ill_said well_said) Tom)
                   :cs [well_said ill_said]})))
        live (mapv #(believed-firings kb (:cs %)) runs)
        back (let [k (doto (tu/test-kb) (v/recover))]
               (mapv #(believed-firings k (:cs %)) runs))]
    (doseq [[{:keys [row order fired]} l b] (map vector runs live back)]
      (is (= #{fired} (set (keys l)))
          (str row " " (vec order) " fires its one rule"))
      (is (= l b) (str row " " (vec order) ": live " (pr-str l) ", recovered " (pr-str b))))))

(tu/deftest-kb ^:slow a-predication-firing-reads-the-same-after-a-restart
  ;; all 24 orders of each row
  (restart-readings! kb (oi/permutations [:rule :fact :kind :edge])))

(tu/deftest-kb a-predication-firing-reads-the-same-after-a-restart-in-sampled-orders
  ;; the sampled twin: the four orders that put each statement last
  (restart-readings! kb [[:fact :kind :edge :rule] [:rule :kind :edge :fact]
                         [:rule :fact :edge :kind] [:rule :fact :kind :edge]]))

;; The join asks a kind goal at the contexts of the head's memberships, which hold no
;; source of the prover's, so the firing lands where the membership and the fact meet.
(tu/deftest-kb a-head-kind-stated-in-a-context-classifies-for-its-readers-only
  (v/assert kb (list 'unreifiable_function Quote) 'CxUniverse)
  (doseq [kind-first? [true false]]
    (tu/with-terms [dog said asserter Tom CxA CxReader CxOther]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxReader CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxOther 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'implies (list 'and (list said '?a '?q) (list 'predication '?q))
                         (list asserter '?a))
                'CxUniverse {:direction :forward})
      (let [kind #(v/assert kb (list 'predicate dog) CxA)]
        (when kind-first? (kind))
        (doseq [c [CxReader CxOther]]
          (v/assert kb (list said Tom (list Quote (list dog 'Muffet))) c))
        (when-not kind-first? (kind)))
      (is (= [true false]
             [(v/ask? kb (list asserter Tom) CxReader) (v/ask? kb (list asserter Tom) CxOther)])
          (str "kind first " kind-first?)))))

;; ---- argN: a position inside a written formula ------------------------------------
;; `provers/ArgPositionProver` reads `(argN term n formula)` off how the formula is
;; written: core.txt's `(quotedArg argN 3 formula)` takes it as a mention.

(tu/deftest-kb argn-answers-the-positions-of-a-written-formula
  (tu/with-terms [parentOf dog Tom Bob]
    (let [ans (fn [goal] (set (v/query kb goal 'CxUniverse)))]
      (is (= #{{'?t parentOf '?n 0} {'?t Tom '?n 1} {'?t Bob '?n 2}}
             (ans (list 'argN '?t '?n (list parentOf Tom Bob)))))
      (is (v/ask? kb (list 'argN Bob 2 (list parentOf Tom Bob)) 'CxUniverse))
      (is (not (v/ask? kb (list 'argN Bob 1 (list parentOf Tom Bob)) 'CxUniverse)))
      (is (= #{{'?t (list dog Tom)}} (ans (list 'argN '?t 1 (list 'not (list dog Tom)))))
          "a connective's operand is the term at its position")
      (is (= #{{'?n 2}} (ans (list 'argN Bob '?n (list parentOf '?x Bob))))
          "an open formula answers the positions of the pattern as written")
      (is (= #{{'?t Tom '?n 1}} (ans (list 'argN '?t '?n (list '?r Tom))))
          "a variable operator answers no position 0"))))

(tu/deftest-kb an-argn-antecedent-fires-in-either-arrival-order-and-withdraws-with-the-fact
  (doseq [rule-first? [true false]]
    (tu/with-terms [parentOf said mentions Tom Ann Bob]
      (v/assert kb (list 'quotedArg said 2 'formula) 'CxUniverse)
      (let [rule #(v/assert kb (list 'implies (list 'and (list said '?a '?f) (list 'argN '?t 1 '?f))
                                     (list mentions '?a '?t))
                            'CxUniverse {:direction :forward})
            _    (when rule-first? (rule))
            h    (v/assert kb (list said Tom (list parentOf Ann Bob)) 'CxUniverse)]
        (when-not rule-first? (rule))
        (is (v/ask? kb (list mentions Tom Ann) 'CxUniverse) (str "rule first " rule-first?))
        (is (not (v/ask? kb (list mentions Tom Bob) 'CxUniverse)))
        (v/retract! kb h)
        (is (not (v/ask? kb (list mentions Tom Ann) 'CxUniverse))
            (str "rule first " rule-first? ": withdrawn with the fact"))))))

(tu/deftest-kb a-backward-argn-antecedent-is-proved-once-its-formula-is-bound
  ;; nothing stores an argN row, so the index model alone would run the argN conjunct first
  (tu/with-terms [parentOf said mentions Tom Ann Bob]
    (v/assert kb (list 'quotedArg said 2 'formula) 'CxUniverse)
    (v/assert kb (list said Tom (list parentOf Ann Bob)) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list said '?a '?f) (list 'argN '?t 1 '?f))
                       (list mentions '?a '?t))
              'CxUniverse)
    (is (= #{{'?t Ann}} (set (v/prove kb (list mentions Tom '?t) 'CxUniverse))))
    (is (= #{{'?t Ann '?f (list parentOf Ann Bob)}}
           (set (v/prove kb [(list 'argN '?t 1 '?f) (list said Tom '?f)] 'CxUniverse)))
        "a conjunction written with argN first")))

;; A formula reached through a quoting function answers the positions of the form it names,
;; written out or minted to a constant whose `natFormula` the firing then rests on.
(tu/deftest-kb argn-reads-the-form-a-quoted-formula-names
  (doseq [reifiable? [false true]]
    (tu/with-terms [parentOf said mentions Tom Ann Bob]
      (let [d (when reifiable? (v/assert kb (list 'reifiable_function Quote) 'CxUniverse))
            _ (v/assert kb (list 'implies (list 'and (list said '?a '?f) (list 'argN '?t 1 '?f))
                                 (list mentions '?a '?t))
                        'CxUniverse {:direction :forward})
            h (v/assert kb (list said Tom (list Quote (list parentOf Ann Bob))) 'CxUniverse)
            f (nth (:sentence (v/sentex kb h)) 2)]
        (is (= reifiable? (nat-read/reified-nat-symbol? f)))
        (is (= #{{'?t parentOf '?n 0} {'?t Ann '?n 1} {'?t Bob '?n 2}}
               (set (v/query kb (list 'argN '?t '?n f) 'CxUniverse)))
            (str "reifiable " reifiable?))
        (is (v/ask? kb (list mentions Tom Ann) 'CxUniverse) (str "reifiable " reifiable?))
        (v/retract! kb h)
        (is (not (v/ask? kb (list mentions Tom Ann) 'CxUniverse)) (str "reifiable " reifiable?))
        (when d (v/retract! kb d))))))

;; ---- closedness: a variable inside (Quote …) is not free around it ----------------
;; `sx/ground?` answers whether a sentence holds any variable at all.  `sx/closed?` answers
;; whether a sentence has a free variable: one bound by an enclosing quantifier, or one
;; inside a (Quote …), is not free (vaelii/vaelii#160).

(defn- lit
  "A sentex map holding `sentence`, the shape `sx/ground?` and `sx/closed?` read."
  [sentence]
  {:sentence sentence})

(deftest closed-reads-quote-and-quantifiers-as-binding-and-ground-reads-neither
  (testing "a variable-free sentence is ground and closed"
    (is (sx/ground? (lit '(dog Muffet))))
    (is (sx/closed? (lit '(dog Muffet)))))
  (testing "a free variable makes a sentence neither"
    (is (not (sx/ground? (lit '(dog ?x)))))
    (is (not (sx/closed? (lit '(dog ?x))))))
  (testing "a variable inside a Quote is part of the quoted form"
    (is (not (sx/ground? (lit '(awesome_rule (Quote (implies (poodle ?x) (dog ?x))))))))
    (is (sx/closed? (lit '(awesome_rule (Quote (implies (poodle ?x) (dog ?x)))))))
    (is (sx/closed? (lit '(variable (Quote ?x))))))
  (testing "a variable a quantifier binds is not free"
    (is (sx/closed? (lit '(forall ?x (implies (dog ?x) (animal ?x))))))
    (is (sx/closed? (lit '(thereExists ?x (dog ?x)))))
    (is (sx/closed? (lit '(exists (?x ?y) (parentOf ?x ?y))))))
  (testing "a variable outside the Quote or the quantifier stays free"
    (is (not (sx/closed? (lit '(likes ?y (Quote (dog ?x)))))))
    (is (not (sx/closed? (lit '(thereExists ?x (likes ?x ?y)))))))
  (testing "a Quasiquote is no Quote: its variables are meant to be bound from outside"
    (is (not (sx/closed? (lit '(holds (Quasiquote (dog ?x)))))))))

;; ---- a quoted rule is a closed fact, storable like any other mention ---------------
;; awesome_rule's argument holds an (implies ...) form as syntax: the ?x inside the Quote
;; is part of the quoted form, never free in the sentence around it, so the outer sentence
;; is closed and stores.  check-ground reads `sx/closed?`, which treats a (Quote …) as
;; opaque (vaelii/vaelii#160).
(tu/deftest-kb a-quoted-rule-is-closed-and-storable
  ;; The real Quote, not a fresh stand-in: closedness reads the form's syntax, and a
  ;; quoting form is spelled (Quote …).
  (tu/with-terms [awesome_rule]
    (v/assert kb (list 'reifiable_function 'Quote) 'CxUniverse)
    (v/assert kb (list 'unary_predicate awesome_rule) 'CxUniverse)
    (v/assert kb (list 'arg awesome_rule 1 'formula)  'CxUniverse)
    (let [quoted-rule (list 'Quote (list 'implies (list 'poodle '?x) (list 'dog '?x)))
          stored      (try (v/assert kb (list awesome_rule quoted-rule) 'CxUniverse)
                           (catch clojure.lang.ExceptionInfo _ nil))]
      (testing "the quoted rule form stores as a closed sentence"
        (is (some? stored))))))

;; A query's ?x and the ?x inside a stored (Quote …) are different things: the query's is
;; a variable, the stored one is part of a constant.  Matching once bound the query's ?x
;; to the quoted ?x, and resolving {?x ?x} overflowed the stack (vaelii/vaelii#167).
(tu/deftest-kb a-quoted-variable-matches-only-the-same-quoted-variable
  (tu/with-terms [awesome_rule]
    (v/assert kb (list 'unary_predicate awesome_rule) 'CxUniverse)
    (let [quoted (fn [v] (list 'Quote (list 'implies (list 'poodle v) (list 'dog v))))]
      (v/assert kb (list awesome_rule (quoted '?x)) 'CxUniverse)
      (is (true? (v/ask? kb (list awesome_rule (quoted '?x)) 'CxUniverse))
          "the stored spelling, its variable named as the query's")
      (is (false? (v/ask? kb (list awesome_rule (quoted '?y)) 'CxUniverse))
          "(Quote … ?y …) is a different expression")
      (is (false? (v/ask? kb (list awesome_rule (quoted 'Muffet)) 'CxUniverse))
          "a quoted variable is not bound by a constant")
      (is (= [{'?r (quoted '?x)}] (v/ask kb (list awesome_rule '?r) 'CxUniverse))))))

(tu/deftest-kb sameas-does-not-fold-a-quoted-term
  ;; The opacity: merging the *referents* Muffet and Fluffet leaves the two *terms* — and
  ;; so the two reified quoted constants — distinct, because a mention tracks identity of
  ;; the symbol, not of what it denotes.
  (tu/with-terms [Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote Muffet))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote Fluffet)) 'CxUniverse))]
      (is (not= k1 k2))
      (v/assert kb (list 'sameAs Muffet Fluffet) 'CxUniverse)
      (testing "the referents merge but the quoted terms do not"
        (is (empty? (nat/colliding-constant-groups kb)) "no collision is minted")
        (is (= (list Quote Muffet)  (nat/nat-expression kb k1)) "K1 still quotes Muffet")
        (is (= (list Quote Fluffet) (nat/nat-expression kb k2)) "K2 still quotes Fluffet")
        (is (not (v/same-class? kb k1 k2)) "and the two quoted constants stay distinct")))))

(tu/deftest-kb rewriteof-does-fold-a-quoted-term
  ;; The spelling half: `(rewriteOf Fluffet Muffet)` retires the *spelling* Muffet, so
  ;; `(Quote Muffet)` migrates to `(Quote Fluffet)` and the two constants collide and merge
  ;; — the existing NAT-rename behaviour, reaching into the mention because it is a rename.
  (tu/with-terms [Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote Muffet))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote Fluffet)) 'CxUniverse))]
      (is (not= k1 k2))
      (v/assert kb (list 'rewriteOf Fluffet Muffet) 'CxUniverse)   ; Muffet deprecated -> Fluffet
      (testing "the quoted expression is rewritten by the spelling rename and folds"
        (is (empty? (nat/colliding-constant-groups kb)) "the collision is repaired to one")
        (is (some? (nat-read/dedup-constant kb (list Quote Fluffet))))
        (is (= (nat-read/dedup-constant kb (list Quote Fluffet))
               (nat-read/dedup-constant kb (list Quote Muffet)))
            "the retired spelling still resolves to the merged constant")))))

(tu/deftest-kb a-non-quoting-reifiable-nat-still-folds-on-a-spelling-merge
  ;; Control: mention opacity is specific to the quoting functions.  A plain reifiable NAT's
  ;; expression is rewritten by the ordinary full-representative walk, unchanged by this work.
  (tu/with-terms [FruitFn AppleTree MalusTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [k (k-of kb (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse))]
      (v/assert kb (list 'rewriteOf MalusTree AppleTree) 'CxUniverse)
      (is (= (list FruitFn MalusTree) (nat/nat-expression kb k))
          "a non-quoting NAT's expression still migrates"))))

;; ---- opacity holds all the way down --------------------------------------
;; The `spelling?` flag "turns on at a quoting function's arguments and stays on all the
;; way down — the whole quoted expression is syntax", so a referent nested inside the
;; mention is as opaque to an identity merge as one at its top level, and a spelling
;; rename reaches it just the same.  The bare-symbol tests above assert depth 1; these assert
;; the recursion.

(tu/deftest-kb sameas-does-not-fold-a-referent-nested-in-a-quoted-compound
  (tu/with-terms [foo Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote (list foo Muffet)))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote (list foo Fluffet))) 'CxUniverse))]
      (is (not= k1 k2))
      (v/assert kb (list 'sameAs Muffet Fluffet) 'CxUniverse)
      (testing "the nested referents merge but the quoted compounds stay distinct"
        (is (empty? (nat/colliding-constant-groups kb)) "no collision is minted")
        (is (= (list Quote (list foo Muffet))  (nat/nat-expression kb k1)))
        (is (= (list Quote (list foo Fluffet)) (nat/nat-expression kb k2)))
        (is (not (v/same-class? kb k1 k2)))))))

(tu/deftest-kb rewriteof-folds-a-spelling-nested-in-a-quoted-compound
  (tu/with-terms [foo Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote (list foo Muffet)))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote (list foo Fluffet))) 'CxUniverse))]
      (is (not= k1 k2))
      (v/assert kb (list 'rewriteOf Fluffet Muffet) 'CxUniverse)   ; nested Muffet -> Fluffet
      (testing "the nested spelling rename reaches into the mention and folds it"
        (is (empty? (nat/colliding-constant-groups kb)))
        (is (= (nat-read/dedup-constant kb (list Quote (list foo Fluffet)))
               (nat-read/dedup-constant kb (list Quote (list foo Muffet)))))))))

(tu/deftest-kb a-transitive-spelling-chain-folds-a-quoted-term
  ;; `spelling-representative` walks the whole rewriteOf-connected component, so a two-hop
  ;; rename `A -> B -> C` resolves `(Quote A)` to `(Quote C)` — the single-hop test above
  ;; leaves the loop unexercised.
  (tu/with-terms [A B C cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [ka (k-of kb (v/assert kb (list cycl_constant (list Quote A)) 'CxUniverse))
          kc (k-of kb (v/assert kb (list cycl_constant (list Quote C)) 'CxUniverse))]
      (is (not= ka kc))
      (v/assert kb (list 'rewriteOf B A) 'CxUniverse)   ; A -> B
      (v/assert kb (list 'rewriteOf C B) 'CxUniverse)   ; B -> C
      (testing "the two-hop spelling chain reaches the mention and folds it"
        (is (empty? (nat/colliding-constant-groups kb)))
        (is (= (nat-read/dedup-constant kb (list Quote C))
               (nat-read/dedup-constant kb (list Quote A)))
            "the head of the chain still resolves the retired spelling")))))

;; ---- orthogonality: quoting is not reifiability --------------------------
;; Quoting governs argument opacity, not whether the application is minted: `Quote`
;; declared unreifiable is still quoting, and `Quasiquote`, declared nothing, is too.  So
;; the combination the reifiable `Quote` tests never reach is a mention that stays
;; structural — never minted — yet whose referents an identity merge still may not fold.

(tu/deftest-kb an-unreifiable-quoter-keeps-a-structural-mention-opaque
  (tu/with-terms [PlainFn Muffet Fluffet Obj p]
    (v/assert kb (list 'unreifiable_function Quote)   'CxUniverse)
    (v/assert kb (list 'unreifiable_function PlainFn) 'CxUniverse)
    (v/assert kb (list 'sameAs Muffet Fluffet)        'CxUniverse)
    (testing "the quoting mention stays structural — never minted"
      (let [h (v/assert kb (list p Obj (list Quote Muffet)) 'CxUniverse)]
        (is (= (list p Obj (list Quote Muffet)) (:sentence (v/sentex kb h))))
        (is (nil? (nat-read/dedup-constant kb (list Quote Muffet))))))
    (testing "and a sameAs merge does not make two quoted mentions congruent"
      (is (v/ask? kb (list 'different (list Quote Muffet) (list Quote Fluffet))
                  'CxUniverse)))
    (testing "nor two Quasiquote mentions, which no statement declares anything of"
      (is (v/ask? kb (list 'different (list Quasiquote Muffet) (list Quasiquote Fluffet))
                  'CxUniverse)))
    (testing "while a non-quoting unreifiable function's arguments still fold"
      (is (not (v/ask? kb (list 'different (list PlainFn Muffet) (list PlainFn Fluffet))
                       'CxUniverse))))))

;; ---- the mention walk does not disturb ordinary congruence ----------------

(tu/deftest-kb quoting-does-not-block-ordinary-congruence
  ;; The mention walk is the congruence walk in every KB, but a NON-quoting compound must
  ;; still fold under a sameAs identity merge — the mention only spelling-restricts a
  ;; quoting head's own arguments.  A regression defaulting the walk to spelling would
  ;; break `(F 5 Kilogram) = (F 5 Kg)` congruence.
  (tu/with-terms [Kilogram Kg QuantityFn cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (v/assert kb (list 'sameAs Kilogram Kg) 'CxUniverse)
    (let [q (fn [u] (list QuantityFn 5 u))]
      (testing "a non-quoting compound still folds under congruence"
        (is (not (v/ask? kb (list 'different (q Kilogram) (q Kg)) 'CxUniverse))))
      (testing "and an unmerged magnitude still tells two compounds apart"
        (is (v/ask? kb (list 'different (q Kilogram) (list QuantityFn 6 Kg)) 'CxUniverse))))))

;; ---- recover -------------------------------------------------------------

(tu/deftest-kb mention-opacity-survives-recover
  ;; the quoting functions are the engine's, not a stored mark, so a rebuild has nothing to
  ;; reconstruct for them — a recovered KB holds a mention opaque exactly as the running
  ;; one did, and a restart changes no answer.
  (tu/with-terms [Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote Muffet))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote Fluffet)) 'CxUniverse))]
      (v/recover kb)
      (testing "Quote is still a quoting function"
        (is (contains? (:quoting (tax/mention-marks (reasoning/taxonomy kb))) Quote)))
      (testing "so the mention is still opaque to an identity merge after recovery"
        (v/assert kb (list 'sameAs Muffet Fluffet) 'CxUniverse)
        (is (empty? (nat/colliding-constant-groups kb)))
        (is (not (v/same-class? kb k1 k2)))))))

;; ---- opacity reaches the REIFY pass, not only congruence ------------------
;; A compound mention whose payload contains a reifiable_function must not have that inner
;; NAT reified *by identity* — `reify-or-mint-nat` would otherwise fold two quoted syntaxes
;; whose payloads' referents merged onto one constant, before congruence could protect them.

(tu/deftest-kb a-reifiable-payload-inside-a-quote-is-not-folded-by-a-sameas
  (tu/with-terms [foo Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (v/assert kb (list 'reifiable_function foo) 'CxUniverse)   ; the payload's inner functor reifies
    (v/assert kb (list 'sameAs Muffet Fluffet) 'CxUniverse)   ; referents merged FIRST
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote (list foo Muffet)))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote (list foo Fluffet))) 'CxUniverse))]
      (testing "the two quoted syntaxes stay distinct — the inner NAT is not reified by identity"
        (is (not= k1 k2))
        (is (= (list Quote (list foo Muffet))  (nat/nat-expression kb k1)) "K1 keeps (foo Muffet) literal")
        (is (= (list Quote (list foo Fluffet)) (nat/nat-expression kb k2)) "K2 keeps (foo Fluffet) literal")))))

(tu/deftest-kb a-quoted-reifiable-payload-is-retrievable-on-read
  ;; The read leaf must hold a mention opaque exactly as the write leaf does.  A quoted
  ;; payload with a reifiable inner functor is stored against its LITERAL form; if the read
  ;; goal reified that inner NAT it would probe for `(Quote <constant>)`, never stored, and
  ;; the fact would read back as no-match — stored-but-unretrievable.
  (tu/with-terms [foo bar Muffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (v/assert kb (list 'reifiable_function foo) 'CxUniverse)   ; the quoted payload's functor reifies
    (v/assert kb (list cycl_constant (list Quote (list foo Muffet))) 'CxUniverse)
    (testing "the exact quoted-payload fact round-trips through the read path"
      (is (= 1 (count (v/sentexes-matching kb (list cycl_constant (list Quote (list foo Muffet)))
                                           'CxUniverse)))
          "queried by its literal mention form")
      (is (v/ask? kb (list cycl_constant (list Quote (list foo Muffet))) 'CxUniverse)))
    (testing "still retrievable when the inner expression is ALSO minted as an object NAT elsewhere"
      (v/assert kb (list bar (list foo Muffet)) 'CxUniverse)   ; forces (foo Muffet) to a real constant
      (is (v/ask? kb (list cycl_constant (list Quote (list foo Muffet))) 'CxUniverse)
          "the read still resolves against the literal mention, not the object constant"))))

(tu/deftest-kb why-not-reports-only-the-terms-a-mention-aware-rewrite-moves
  ;; The `why-not` displacement map (`displaced-terms`) must agree with what `rewrite-term*`
  ;; actually rewrites.  A used term moved by a `rewriteOf` is reported; a term quoted inside
  ;; a mention, whose referent merged under a `sameAs`, is held opaque by the rewrite and must
  ;; NOT be reported displaced — else why-not cites a merge that never touched the sentence.
  ;; The flat walk over-reported it; the mention-aware collector does not.
  (tu/with-terms [knows Bob Rob Ann Zed cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (v/assert kb (list 'rewriteOf Rob Bob) 'CxUniverse)   ; used term Bob -> Rob (a spelling rename)
    (v/assert kb (list 'sameAs Ann Zed) 'CxUniverse)      ; quoted term Zed's referent merges (identity)
    (let [d (kb/displaced-terms kb (list knows Bob (list Quote Zed)) 'CxUniverse)]
      (is (= Rob (get d Bob)) "the used term is reported displaced by its spelling rename")
      (is (not (contains? d Zed))
          "the quoted mention is held opaque to the sameAs and is not reported displaced"))))

;; ---- quoting is fixed by the engine, not declared --------------------------

;; ---- quoting is fixed by the engine, not declared --------------------------
;; `Quote` and `Quasiquote` are the quoting functions (`sx/quoting-functors`).  No KB
;; predicate declares a function quoting: `quoting_function` is not vocabulary, so a
;; sentence on it is an ordinary fact on an undeclared predicate and marks nothing.

(tu/deftest-kb quoting-function-is-not-vocabulary
  (tu/with-terms [PlainFn Muffet Fluffet]
    (testing "the predicate is not declared"
      (is (empty? (v/sentexes-matching kb '(unary_predicate quoting_function) '?ctx)))
      (is (empty? (v/sentexes-matching kb '(comment quoting_function ?c) '?ctx))))
    (testing "a sentence on it is stored as an ordinary fact that marks nothing"
      (v/assert kb (list 'quoting_function PlainFn) 'CxUniverse)
      (is (= #{Quote Quasiquote} (:quoting (tax/mention-marks (reasoning/taxonomy kb)))))
      (v/assert kb (list 'unreifiable_function PlainFn) 'CxUniverse)
      (v/assert kb (list 'sameAs Muffet Fluffet) 'CxUniverse)
      (is (not (v/ask? kb (list 'different (list PlainFn Muffet) (list PlainFn Fluffet))
                       'CxUniverse))
          "so the function it names folds under an identity merge like any other"))))

(deftest a-fresh-kb-holds-a-quote-mention-opaque-with-no-declaration
  ;; An empty KB states nothing about `Quote`, and the mention is still opaque from the
  ;; first assert: the merge of the referents leaves the two quoted terms apart.
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (v/assert kb '(mentions Obj (Quote Muffet)) 'CxUniverse)
    (v/assert kb '(mentions Obj (Quote Fluffet)) 'CxUniverse)
    (v/assert kb '(sameAs Muffet Fluffet) 'CxUniverse)
    (testing "the referents merge"
      (is (v/same-class? kb 'Muffet 'Fluffet)))
    (testing "the quoted terms do not"
      (is (v/ask? kb '(different (Quote Muffet) (Quote Fluffet)) 'CxUniverse))
      (is (= #{'(mentions Obj (Quote Muffet)) '(mentions Obj (Quote Fluffet))}
             (into #{} (map :sentence) (v/sentexes-matching kb '(mentions Obj ?q) 'CxUniverse)))
          "both spellings are still stored as written"))))

(deftest a-never-minted-quotation-stays-as-written-under-a-reifiable-function-declaration
  ;; `(reifiable_function Quote)` makes `Quote` reifiable, and a quotation stored only
  ;; as a `modal_predicate`'s proposition is never minted.  The read keeps the goal's
  ;; `(Quote X)` as written, so the definitional `different` answers for it.
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (v/assert kb '(modal_predicate believes) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(reifiable_function Quote) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(result Quote cycl_expression) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(believes Obj (Quote Muffet)) 'CxUniverse)
    (v/assert kb '(believes Obj (Quote Fluffet)) 'CxUniverse)
    (testing "before the merge"
      (is (v/ask? kb '(different (Quote Muffet) (Quote Fluffet)) 'CxUniverse)))
    (v/assert kb '(sameAs Muffet Fluffet) 'CxUniverse)
    (testing "after the merge"
      (is (v/ask? kb '(different (Quote Muffet) (Quote Fluffet)) 'CxUniverse)))))
