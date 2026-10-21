;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.equational-test
  "Symbolic (schematic) equational reasoning — the gap docs/equality.md names.

  Two pieces, on top of ground congruence (which is already free — a `(equals a b)`
  over symbols rewrites every sentex mentioning `a`, at any nesting, via the inverted
  term index; see `ground-congruence-is-free` below):

  * **Part A — compound equality over reifiable NATs.**  `(equals (MotherOf Alice)
    (MotherOf Bob))` — *Alice and Bob have the same mother, so they are siblings* —
    is accepted when `MotherOf` is a `reifiable_function`.  It reduces to ordinary
    individual equality: each side reifies to its constant *before* wff runs
    (docs/nat.md), so `(equals K1 K2)` merges in the partition and a fact about one
    holds of the other.  A compound equality that does **not** reduce — a structural NAT
    measure like `(QuantityFn 5 Kilogram)` — stays refused.

  * **Part B — schematic equational rules.**  `(equals (fatherOf (fatherOf ?x))
    (grandfather_of ?x))` is an oriented rewrite `fatherOf∘fatherOf → grandfather_of`.
    A stored `(parent_chain (fatherOf (fatherOf Tom)))` normalizes to `(parent_chain
    (grandfather_of Tom))`, so a query on the `grandfather_of` normal form matches.
    Oriented by a reduction order (strict size decrease + the variable condition), so
    rewriting terminates.

  Both are belief-following: every rewrite is a JTMS-justified twin, so retracting
  the equation collects the rewrites and revives the originals — exactly the
  discipline ground migration already has.

  House rules: gensym'd temporaries via `tu/with-terms`; engine vocabulary
  (`equals`, `reifiable_function`, `QuantityFn`, `Kilogram`, contexts) literal; the
  neutral fixture asserts the KB is restored.  CxUniverse is loaded because the NAT
  bookkeeping (`natFormula`, `result`) rides real vocabulary."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

;; ---- baseline: ground congruence is already free ------------------------

(tu/deftest-kb ground-congruence-is-free
  ;; `(equals a b)` over two symbols rewrites every sentex naming `a` to `b` at any
  ;; nesting — no congruence algorithm, just the term index + migration.
  (tu/with-terms [bornIn Obama BarackObama Honolulu]
    (v/assert kb (list bornIn Obama Honolulu) 'CxUniverse)
    (v/assert kb (list 'equals Obama BarackObama) 'CxUniverse)
    (is (= [{'?c Honolulu}] (v/ask kb (list bornIn BarackObama '?c) 'CxUniverse))
        "a fact about Obama holds of the merged BarackObama")))

;; ---- Part A: compound equality over reifiable NATs ----------------------

(tu/deftest-kb reifiable-compound-equality-merges-the-reified-nats
  ;; (equals (MotherOf Alice) (MotherOf Bob)): Alice and Bob share a mother.  Each
  ;; side reifies to a reified NAT constant before wff, so this is ordinary individual
  ;; equality — the two reified NATs merge and a fact about one holds of the other.
  (tu/with-terms [MotherOf Alice Bob livesIn NYC]
    (v/assert kb (list 'reifiable_function MotherOf) 'CxUniverse)
    (v/assert kb (list livesIn (list MotherOf Alice) NYC) 'CxUniverse)
    (testing "before the merge, nothing is known about Bob's mother"
      (is (empty? (v/ask kb (list livesIn (list MotherOf Bob) '?c) '?ctx))))
    (let [h (v/assert kb (list 'equals (list MotherOf Alice) (list MotherOf Bob))
                      'CxUniverse)]
      (testing "the assertion is accepted, its sides reified to symbols"
        (is (some? h))
        (is (every? nat/reified-nat-symbol? (rest (:sentence (v/sentex kb h))))))
      (testing "the reified NATs merge — a fact about Alice's mother holds of Bob's"
        (is (= [{'?c NYC}] (v/ask kb (list livesIn (list MotherOf Bob) '?c) 'CxUniverse))))
      (testing "and they resolve to one class"
        (is (v/same-class? kb
                           (nat/dedup-constant kb (list MotherOf Alice))
                           (nat/dedup-constant kb (list MotherOf Bob)))))
      (testing "retracting the equation is belief-following: Bob's mother separates,"
        (v/retract! kb h)
        (is (empty? (v/ask kb (list livesIn (list MotherOf Bob) '?c) '?ctx))))
      (testing "and Alice's own fact survives"
        (is (= [{'?c NYC}] (v/ask kb (list livesIn (list MotherOf Alice) '?c) 'CxUniverse)))))))

(tu/deftest-kb structural-nat-compound-equality-is-refused
  ;; A structural NAT measure stays structural (never reified), so `(equals (QuantityFn …)
  ;; (QuantityFn …))` does not reduce to symbol equality and wff refuses the compound
  ;; — measure sameness is `sameQuantity`, a computed comparison, not the closure.
  (testing "equals over two ground QuantityFn measures is refused as not-well-formed"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"compound"
         (v/assert kb '(equals (QuantityFn 5 Kilogram) (QuantityFn 5000 Gram))
                   'CxUniverse)))))

;; ---- Part B: schematic equational rules ---------------------------------

(defn- nest [f base n] (reduce (fn [t _] (list f t)) base (range n)))

(tu/deftest-kb schematic-rewrite-normalizes-store-and-query
  ;; (equals (fatherOf (fatherOf ?x)) (grandfather_of ?x)) orients fatherOf∘fatherOf →
  ;; grandfather_of; a stored (parent_chain (fatherOf (fatherOf Tom))) normalizes so a
  ;; query on the grandfather_of normal form matches.
  (tu/with-terms [fatherOf grandfather_of parent_chain Tom]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
              'CxUniverse)
    (v/assert kb (list parent_chain (list fatherOf (list fatherOf Tom))) 'CxUniverse)
    (testing "the stored term meets a query at the grandfather_of normal form"
      (is (seq (v/sentexes-matching kb (list parent_chain (list grandfather_of Tom)) 'CxUniverse))))
    (testing "a query on the pre-normal form still matches — the goal normalizes too"
      (is (= [(list parent_chain (list grandfather_of Tom))]
             (map :sentence (v/sentexes-matching kb (list parent_chain (list fatherOf (list fatherOf Tom)))
                                                 'CxUniverse)))))
    (testing "ask binds through the normal form"
      (is (= [{'?y Tom}]
             (v/ask kb (list parent_chain (list grandfather_of '?y)) 'CxUniverse))))))

(tu/deftest-kb schematic-rewrite-is-belief-following
  ;; Every rewrite is a JTMS-justified twin, so retracting the equation collects it and
  ;; the original revives — the same discipline ground migration has.
  (tu/with-terms [fatherOf grandfather_of parent_chain Tom]
    (let [he (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x))
                                (list grandfather_of '?x))
                       'CxUniverse)]
      (v/assert kb (list parent_chain (list fatherOf (list fatherOf Tom))) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list parent_chain (list grandfather_of Tom)) 'CxUniverse)))
      (testing "retracting the equation drops the twin and revives the original"
        (v/retract! kb he)
        (is (empty? (v/sentexes-matching kb (list parent_chain (list grandfather_of Tom)) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list parent_chain (list fatherOf (list fatherOf Tom)))
                                      'CxUniverse)))))))

(tu/deftest-kb schematic-rewrite-terminates-on-a-cascade
  ;; The reduction order guarantees termination whatever the nesting depth: fatherOf^6
  ;; Tom reduces to grandfather_of^3 Tom, and normalization does not hang.
  (tu/with-terms [fatherOf grandfather_of ancestry Tom]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
              'CxUniverse)
    (v/assert kb (list ancestry (nest fatherOf Tom 6)) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list ancestry (nest grandfather_of Tom 3)) 'CxUniverse)))))

(tu/deftest-kb schematic-rewrite-is-order-independent
  ;; Both migration paths converge on the same normal form: a fact asserted BEFORE the
  ;; equation is migrated when the rule arrives (migrate-matching); one asserted AFTER
  ;; is migrated on its own assert (migrate-sentex).  Two disjoint term sets exercise
  ;; each order in one KB.
  (tu/with-terms [pa gpa chaina TomA  pb gpb chainb TomB]
    (testing "rule then fact — the fact migrates when it arrives"
      (v/assert kb (list 'equals (list pa (list pa '?x)) (list gpa '?x)) 'CxUniverse)
      (v/assert kb (list chaina (list pa (list pa TomA))) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list chaina (list gpa TomA)) 'CxUniverse))))
    (testing "fact then rule — the stored fact migrates when the rule arrives"
      (v/assert kb (list chainb (list pb (list pb TomB))) 'CxUniverse)
      (v/assert kb (list 'equals (list pb (list pb '?x)) (list gpb '?x)) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list chainb (list gpb TomB)) 'CxUniverse))))))

(tu/deftest-kb prove-and-backward-normalize-the-goal
  ;; Parity: prove/backward now rewrite the top goal like query/ask, so a schematic
  ;; normal form — and a merged (retired) spelling — is answered there too, closing the
  ;; path-dependent-answer gap.
  (tu/with-terms [fatherOf grandfather_of parent_chain Tom  bornIn Keep Retire Hawaii]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
              'CxUniverse)
    (v/assert kb (list parent_chain (list fatherOf (list fatherOf Tom))) 'CxUniverse)
    (testing "prove answers the grandfather_of normal form"
      (is (seq (v/prove kb (list parent_chain (list grandfather_of Tom)) 'CxUniverse))))
    (testing "backward answers the pre-normal form — the goal normalizes"
      (is (seq (v/prove kb (list parent_chain (list fatherOf (list fatherOf Tom)))
                        'CxUniverse))))
    ;; merged-spelling equality parity: rewriteOf makes Retire the deprecated spelling
    (v/assert kb (list bornIn Retire Hawaii) 'CxUniverse)
    (v/assert kb (list 'rewriteOf Keep Retire) 'CxUniverse)
    (testing "prove answers a goal under the retired spelling (goal rewrites to the rep)"
      (is (= [{'?c Hawaii}] (v/prove kb (list bornIn Retire '?c) 'CxUniverse))))))

(tu/deftest-kb schematic-rewrite-orients-equal-size-by-precedence
  ;; KBO orients an equal-size pair by the symbol precedence (where the old size-only
  ;; rule refused).  The direction is content-fixed, so both facts normalize to one
  ;; canonical form and collapse to a single believed sentex.
  (tu/with-terms [ff gg wrap Tom]
    (v/assert kb (list 'equals (list ff (list gg '?x)) (list gg (list ff '?x)))
              'CxUniverse)
    (v/assert kb (list wrap (list ff (list gg Tom))) 'CxUniverse)
    (v/assert kb (list wrap (list gg (list ff Tom))) 'CxUniverse)
    (is (= 1 (count (distinct (map :sentence
                                   (v/sentexes-matching kb (list wrap '?t) 'CxUniverse)))))
        "the two equal-size-related facts collapse to one normal form")))

(tu/deftest-kb schematic-rewrite-orients-a-pair-differing-at-a-constant
  ;; `(equals (UnitFn Meter ?n) (UnitFn Metre ?n))`: same root, same weight, the first
  ;; difference a constant.  KBO decides it on the constants' precedence, so the
  ;; equation is admitted (not refused, and no throw) and both spellings of a fact
  ;; normalize to the one the precedence elects.
  (tu/with-terms [unitFn wrap]
    (let [meter (tu/tmp-ind "Meter") metre (tu/tmp-ind "Metre")
          h (v/assert kb (list 'equals (list unitFn meter '?n) (list unitFn metre '?n))
                      'CxUniverse)]
      (is (some? h) "a constant-differing schematic equation is admitted")
      (v/assert kb (list wrap (list unitFn meter 5)) 'CxUniverse)
      (v/assert kb (list wrap (list unitFn metre 5)) 'CxUniverse)
      (is (= 1 (count (distinct (map :sentence
                                     (v/sentexes-matching kb (list wrap '?t) 'CxUniverse)))))
          "both spellings collapse to one normal form"))))

(tu/deftest-kb schematic-rewrite-orients-a-pair-whose-root-is-itself-compound
  ;; `((ff ?x) a)` is a legal term whose functor is a compound, so the precedence is
  ;; asked to rank two compounds.  It must answer — an equation the order cannot decide
  ;; is refused with a message (`permutative-schematic-equation-is-refused`), and a
  ;; comparison that throws is not a refusal but a crash at the assert entry point.
  (tu/with-terms [ff gg wrap]
    (let [a (tu/tmp-ind "A")
          h (v/assert kb (list 'equals (list (list ff '?x) a) (list (list gg '?x) a))
                      'CxUniverse {:strength :monotonic})]
      (is (some? h) "a compound-rooted schematic equation is admitted, not thrown at")
      (v/assert kb (list wrap (list (list ff a) a)) 'CxUniverse)
      (v/assert kb (list wrap (list (list gg a) a)) 'CxUniverse)
      (is (= 1 (count (distinct (map :sentence
                                     (v/sentexes-matching kb (list wrap '?t) 'CxUniverse)))))
          "both spellings collapse to the one normal form the precedence elects"))))

(tu/deftest-kb schematic-rewrite-composes-with-symbol-merge
  ;; rewrite-term is symbol congruence THEN schematic normalization, so a schematic
  ;; term containing a merged symbol normalizes both in one pass — congruence and
  ;; rewriting compose.
  (tu/with-terms [fatherOf grandfather_of parent_chain Tom Thomas]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
              'CxUniverse)
    (v/assert kb (list parent_chain (list fatherOf (list fatherOf Tom))) 'CxUniverse)
    (v/assert kb (list 'equals Tom Thomas) 'CxUniverse)      ; a symbol merge
    (let [rep (v/representative kb Tom)]
      (is (seq (v/sentexes-matching kb (list parent_chain (list grandfather_of rep)) 'CxUniverse))
          "the fact normalizes under both the merge (Tom→rep) and the rewrite (∘→gp)"))))

(tu/deftest-kb retracting-one-schematic-rule-leaves-the-other
  ;; The rule cache is belief-following per equation handle: dropping one rule stops
  ;; its normalization while another's stands.
  (tu/with-terms [pp gpp qq ggqq wrap Tom]
    (let [r1 (v/assert kb (list 'equals (list pp (list pp '?x)) (list gpp '?x)) 'CxUniverse)]
      (v/assert kb (list 'equals (list qq (list qq '?x)) (list ggqq '?x)) 'CxUniverse)
      (v/assert kb (list wrap (list pp (list pp Tom))) 'CxUniverse)
      (v/assert kb (list wrap (list qq (list qq Tom))) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list wrap (list gpp Tom)) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list wrap (list ggqq Tom)) 'CxUniverse)))
      (testing "retracting the pp-rule stops its normalization but leaves the qq-rule's"
        (v/retract! kb r1)
        (is (empty? (v/sentexes-matching kb (list wrap (list gpp Tom)) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list wrap (list ggqq Tom)) 'CxUniverse)))))))

(tu/deftest-kb conflicting-schematic-rules-surface-non-confluence
  ;; Two equations with the same LHS but different RHS disagree about a shared term.
  ;; Detection, not completion: nothing is dropped (the normal form stays
  ;; deterministic), but the conflict is surfaced in the violations ledger.
  (tu/with-terms [ff gg hh]
    (let [h1 (v/assert kb (list 'equals (list ff (list ff '?x)) (list gg '?x)) 'CxUniverse)
          _  (v/clear-violations! kb)
          h2 (v/assert kb (list 'equals (list ff (list ff '?x)) (list hh '?x)) 'CxUniverse)
          nc (filter #(= :non-confluent (:violation %)) (v/violations kb))]
      (is (= #{[h2 h1]} (set (map (juxt :rule :with) nc)))
          "the second equation conflicts with the first at their shared LHS")
      (is (every? :message nc)))))

(tu/deftest-kb disjoint-schematic-rules-report-no-conflict
  ;; Rules over different predicates never overlap, so no non-confluence is reported.
  (tu/with-terms [ff gg pp qq]
    (v/assert kb (list 'equals (list ff (list ff '?x)) (list gg '?x)) 'CxUniverse)
    (v/clear-violations! kb)
    (v/assert kb (list 'equals (list pp (list pp '?x)) (list qq '?x)) 'CxUniverse)
    (is (not-any? #(= :non-confluent (:violation %)) (v/violations kb)))))

(tu/deftest-kb permutative-schematic-equation-is-refused
  ;; A permutative equation has no terminating orientation under any term order, so it
  ;; is refused before anything is stored (a limit of KBO — AC-rewriting is a
  ;; separate, larger mechanism).
  (tu/with-terms [rel]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"orient"
         (v/assert kb (list 'equals (list rel '?x '?y) (list rel '?y '?x)) 'CxUniverse)))))

;; ---- the rule order is content, whatever the memo does ------------------

(defn- by-role
  "`form` with each temporary replaced by the role it plays, so two runs over disjoint
  gensym'd vocabularies compare as one shape."
  [m form]
  (if (sequential? form) (apply list (map #(by-role m %) form)) (get m form form)))

(tu/deftest-kb overlapping-schematic-rules-normalize-alike-either-order
  ;; Two equations sharing an LHS both apply to `ff∘ff`, so which one wins decides the
  ;; stored normal form.  `tax/rewrite-rules` orders by content, so the winner is a
  ;; function of the pair rather than of which equation was asserted first — the property
  ;; the memoized order has to preserve, since a memo keyed on anything the writer set
  ;; does not move would hand back the order the *first* read happened to see.
  ;;
  ;; Two disjoint term sets spelled alike, each loaded in one arrival order, compared
  ;; through `by-role` so the gensym'd names do not stand in the way.
  (tu/with-terms [ffa gga hha wrapa TomA  ffb ggb hhb wrapb TomB]
    (letfn [(landed [wrap m]
              (->> (v/sentexes-matching kb (list wrap '?t) 'CxUniverse)
                   (map #(by-role m (:sentence %)))
                   set))]
      (testing "the gg-equation first"
        (v/assert kb (list 'equals (list ffa (list ffa '?x)) (list gga '?x)) 'CxUniverse)
        (v/assert kb (list 'equals (list ffa (list ffa '?x)) (list hha '?x)) 'CxUniverse)
        (v/assert kb (list wrapa (list ffa (list ffa TomA))) 'CxUniverse))
      (testing "the hh-equation first"
        (v/assert kb (list 'equals (list ffb (list ffb '?x)) (list hhb '?x)) 'CxUniverse)
        (v/assert kb (list 'equals (list ffb (list ffb '?x)) (list ggb '?x)) 'CxUniverse)
        (v/assert kb (list wrapb (list ffb (list ffb TomB))) 'CxUniverse))
      (let [a (landed wrapa {ffa 'FF gga 'GG hha 'HH wrapa 'WRAP TomA 'TOM})
            b (landed wrapb {ffb 'FF ggb 'GG hhb 'HH wrapb 'WRAP TomB 'TOM})]
        (is (seq a) "the fact is stored under some normal form")
        (is (= a b) "and it is the same normal form in either arrival order")))))

;; ---- a denied instance of a schematic equation --------------------------

(defn- reflexive-denial?
  "Is `sentence` `(not (equals X X))` — a denial of reflexivity?"
  [sentence]
  (and (= 'not (first sentence))
       (let [[f a b] (second sentence)] (and (= 'equals f) (= a b)))))

(tu/deftest-kb a-denied-instance-of-a-schematic-equation-is-inert
  ;; `equals` is on the forced-monotonic roster, so a denial of one ground instance is
  ;; stored as stated and never believed (docs/nmtms.md, "The forced-monotonic roster"):
  ;; the equation rewrites the denied instance as it rewrites every other, in either
  ;; arrival order and at either strength, and no twin denies reflexivity.
  (doseq [strength [:monotonic :default]
          denial-first? [false true]]
    (testing (str strength " denial, denial first: " denial-first?)
      (tu/with-terms [fatherOf grandfather_of other_chain Ann Tom CxA]
        (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse {:strength :monotonic})
        (let [ff       (fn [n] (list fatherOf (list fatherOf n)))
              g        (fn [n] (list grandfather_of n))
              equation (list 'equals (ff '?x) (g '?x))
              denial   (list 'not (list 'equals (ff Tom) (g Tom)))
              deny!    #(v/assert kb denial CxA {:strength strength})
              h        (if denial-first?
                         (let [h (deny!)] (v/assert kb equation CxA) h)
                         (do (v/assert kb equation CxA) (deny!)))]
          (v/assert kb (list other_chain (ff Tom)) CxA {:strength :monotonic})
          (v/assert kb (list other_chain (ff Ann)) CxA {:strength :monotonic})
          (is (some? (v/sentex kb h)) "the denial is stored as stated")
          (is (false? (v/in? kb h)) "and not believed")
          (is (not-any? #(reflexive-denial? (:sentence %)) (v/sentexes-in-context kb CxA))
              "no stored sentex denies reflexivity")
          (is (= [true true true true]
                 [(v/ask? kb (list 'equals (ff Tom) (g Tom)) CxA)
                  (v/ask? kb (list 'equals (ff Ann) (g Ann)) CxA)
                  (v/ask? kb (list other_chain (g Tom)) CxA)
                  (v/ask? kb (list other_chain (g Ann)) CxA)])
              "the equation rewrites the denied instance and every other"))))))

(tu/deftest-kb an-excepted-schematic-equation-leaves-its-context-the-original-spelling
  ;; An `except` of a schematic equation takes it out of rewriting at the contexts that
  ;; read the except (docs/equational.md, "An except of an equation").  The twin rests on
  ;; the equation, so it is hidden there; the original is no longer displaced in its own
  ;; context, so its supersession drops and the fact is read as spelled.  The twin is not
  ;; a premise, and excepting the equation hides no premise stated in the normal form.
  (tu/with-terms [fatherOf grandfather_of eq_chain Ann Cal CxEq]
    (v/assert kb (list 'genlCx CxEq 'CxUniverse) 'CxUniverse {:strength :monotonic})
    (let [ff (fn [n] (list eq_chain (list fatherOf (list fatherOf n))))
          g  (fn [n] (list eq_chain (list grandfather_of n)))
          eh (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
                       CxEq)
          ann (v/assert kb (ff Ann) CxEq {:strength :monotonic})
          cal (v/assert kb (g Cal) CxEq {:strength :monotonic})
          reads (fn [n] [(v/ask? kb (ff n) CxEq) (v/ask? kb (g n) CxEq)
                         (count (v/sentexes-matching kb (ff n) CxEq))
                         (count (v/sentexes-matching kb (g n) CxEq))])]
      (is (= [true true 1 1] (reads Ann)) "before the except both spellings read the twin")
      (let [x (v/assert kb (list 'except (list 'sentexHandle eh)) CxEq {:strength :monotonic})]
        (testing "while the except stands"
          (is (= [true false 1 0] (reads Ann))
              "the fact is answered as spelled, and the equation's normal form is not")
          (is (= [ann] (map :id (v/sentexes-matching kb (ff Ann) CxEq)))
              "the read returns the stated sentex")
          (is (true? (v/in? kb ann)) "the original is believed, no longer superseded")
          (is (= [cal] (map :id (v/sentexes-matching kb (g Cal) CxEq)))
              "a premise stated in the normal form stays readable"))
        (v/retract! kb x)
        (testing "once the except goes"
          (is (= [true true 1 1] (reads Ann)))
          (is (false? (v/in? kb ann)) "the original is superseded again"))))))

(tu/deftest-kb a-fact-stored-under-an-excepted-equation-is-rewritten-when-the-except-goes
  ;; A fact asserted while an except hides the equation from its context is stored as
  ;; spelled, with no twin.  Retracting the except makes the equation visible again and
  ;; normalizes every goal under it, so the settle re-runs the equation's arrival sweep
  ;; (`special/except-move-sweeps`): the fact gets its twin and reads under both spellings.
  (tu/with-terms [fatherOf grandfather_of eq_chain Bob CxEq]
    (v/assert kb (list 'genlCx CxEq 'CxUniverse) 'CxUniverse {:strength :monotonic})
    (let [ff (list eq_chain (list fatherOf (list fatherOf Bob)))
          g  (list eq_chain (list grandfather_of Bob))
          eh (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
                       CxEq)
          x  (v/assert kb (list 'except (list 'sentexHandle eh)) CxEq {:strength :monotonic})
          bob (v/assert kb ff CxEq {:strength :monotonic})
          reads (fn [] [(v/ask? kb ff CxEq) (v/ask? kb g CxEq)
                        (count (v/sentexes-matching kb ff CxEq))
                        (count (v/sentexes-matching kb g CxEq))])]
      (is (= [true false 1 0] (reads)) "under the except the fact reads as spelled")
      (v/retract! kb x)
      (is (= [true true 1 1] (reads)) "after the except both spellings answer the fact")
      (is (false? (v/in? kb bob)) "the original is superseded by its twin"))))

(tu/deftest-kb an-except-below-the-fact-reads-a-copy-of-the-stated-spelling
  ;; The fact and the equation are in `CxUp`, the except in `CxLow` below it.  `CxUp`
  ;; still supersedes the original, and the twin rests on the equation `CxLow` cannot see,
  ;; so migration stores the original's spelling in `CxLow`, justified by `[original,
  ;; equation, except]` (docs/equational.md, "An except of an equation").  A second except
  ;; in `CxUp` hands the original back there, and the reconcile retires the copy.
  (tu/with-terms [fatherOf grandfather_of eq_chain eqSeen Ann Bob CxUp CxLow]
    (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxLow CxUp) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'implies (list eq_chain '?x) (list eqSeen '?x)) CxLow {:direction :forward})
    (let [ff  (fn [n] (list eq_chain (list fatherOf (list fatherOf n))))
          g   (fn [n] (list eq_chain (list grandfather_of n)))
          eh  (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
                        CxUp)
          ann (v/assert kb (ff Ann) CxUp {:strength :monotonic})
          x   (v/assert kb (list 'except (list 'sentexHandle eh)) CxLow {:strength :monotonic})
          _   (v/assert kb (ff Bob) CxUp {:strength :monotonic})
          copy (fn [n] (map :id (v/sentexes-matching kb (ff n) CxLow)))
          reads (fn [n c] [(v/ask? kb (ff n) c) (v/ask? kb (g n) c)])]
      (testing "while the except stands"
        (doseq [n [Ann Bob]]
          (is (= [true true] (reads n CxUp)) "the fact's own context reads both spellings")
          (is (= [true false] (reads n CxLow)) "the reader below reads the stated spelling")
          (is (= 1 (count (copy n))) "from one copy stored in the reader"))
        (is (false? (v/in? kb ann)) "the original stays superseded in its own context")
        (is (true? (v/ask? kb (list eqSeen (list fatherOf (list fatherOf Ann))) CxLow))
            "a forward rule in the reader fires on the copy"))
      (let [c  (first (copy Ann))
            x2 (v/assert kb (list 'except (list 'sentexHandle eh)) CxUp {:strength :monotonic})]
        (testing "a second except in the fact's own context"
          (is (true? (v/in? kb ann)) "hands the original back")
          (is (false? (v/in? kb c)) "and retires the copy")
          (is (= [true false] (reads Ann CxLow))))
        (v/retract! kb x2)
        (is (= [false true] [(v/in? kb ann) (v/in? kb c)]) "retracting it restores the copy")
        (v/retract! kb x)
        (testing "once the except below goes"
          (doseq [n [Ann Bob]]
            (is (= [true true] (reads n CxLow)))
            (is (empty? (copy n)) "the copy is gone"))
          (is (nil? (v/sentex kb c))))))))

(tu/deftest-kb an-except-below-a-ground-merge-reads-a-copy-of-the-stated-spelling
  ;; The ground analogue: `(gq Beta)` is superseded in `CxUp` by `(gq Alpha)`, and a
  ;; reader below that excepts the merge reads `(gq Beta)` from its copy.
  (doseq [eq '[equals sameAs rewriteOf]]
    (tu/with-terms [gq Alpha Beta CxUp CxLow]
      (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genlCx CxLow CxUp) 'CxUniverse {:strength :monotonic})
      (let [fh (v/assert kb (list gq Beta) CxUp {:strength :monotonic})
            eh (v/assert kb (list eq Alpha Beta) CxUp {:strength :monotonic})
            x  (v/assert kb (list 'except (list 'sentexHandle eh)) CxLow {:strength :monotonic})
            reads (fn [c] [(v/ask? kb (list gq Beta) c) (v/ask? kb (list gq Alpha) c)])]
        (is (= [true true] (reads CxUp)) eq)
        (is (false? (v/in? kb fh)) eq)
        (is (= [true false] (reads CxLow)) eq)
        (is (= 1 (count (v/sentexes-matching kb (list gq Beta) CxLow))) eq)
        (v/retract! kb x)
        (is (= [true true] (reads CxLow)) eq)
        (v/retract! kb eh)
        (v/retract! kb fh)))))
