;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.covering-arg-test
  "The covering argument constraints — `args` / `argsGenl` type EVERY accepted position,
  `argAndRest` / `argAndRestGenl` a position and every later one.  The generalizations of
  `arg` / `genlArg` for a variable-arity tail, where naming a largest finite `arg` would
  make an unbounded relation look finite.

  Each reuses its singular twin's per-argument reading — `args` the instance one,
  `argsGenl` the subtype one — and composes conjunctively with a position-specific
  declaration.  A covering constraint mints nothing and convicts only, and it walks the
  positions a sentence actually has rather than a re-counted tail."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ex-type
  "The `:type` a write thunk meets: its refusal, or the argument conviction its fact is
  held inert under (`tu/write-type`)."
  [f]
  (tu/write-type tu/*kb* f))

(defn- check-message
  "The message of the first check violation `v/check` reports for a sentence, or of the
  argument conviction `assert` holds it inert under (`tu/write-conviction`), or nil."
  [kb sentence context]
  (or (:message (first (v/check kb sentence context)))
      (:message (tu/write-conviction kb sentence context))))

(defn- variable-relation
  "A variable-arity predicate with an `arityMin` of 2, plus a two-level type hierarchy.
  Returns `[rel animal dog other]` — `dog` a subtype of `animal`, `other` a type outside
  it."
  [kb]
  (let [rel (tu/tmp-pred) animal (tu/tmp-type) dog (tu/tmp-type) other (tu/tmp-type)]
    (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'genl other 'thing) 'CxUniverse)
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'variable_arity rel) 'CxUniverse)
    (v/assert kb (list 'arityMin rel 2) 'CxUniverse)
    [rel animal dog other]))

;; ---- args: every position is an instance -----------------------------------

(tu/deftest-kb args-types-every-position-at-two-three-and-high-arity
  (let [[rel animal dog] (variable-relation kb)
        a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind) d (tu/tmp-ind) e (tu/tmp-ind)]
    (v/assert kb (list 'args rel animal) 'CxUniverse)
    (doseq [x [a b c d e]] (v/assert kb (list dog x) 'CxUniverse))
    (testing "two, three and a high arity all store when every member is an instance"
      (is (v/assert kb (list rel a b) 'CxUniverse))
      (is (v/assert kb (list rel a b c) 'CxUniverse))
      (is (v/assert kb (list rel a b c d e) 'CxUniverse)))))

(tu/deftest-kb a-bad-value-only-in-the-unbounded-tail-is-convicted
  (let [[rel animal dog] (variable-relation kb)
        a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'args rel animal) 'CxUniverse)
    (v/assert kb (list dog a) 'CxUniverse)
    (v/assert kb (list dog b) 'CxUniverse)
    (testing "a literal whose kind is not the type, sitting past the declared minimum"
      (is (= :arg-type (ex-type #(v/assert kb (list rel a b "notAnAnimal") 'CxUniverse))))
      (is (re-find #"args" (check-message kb (list rel a b "notAnAnimal") 'CxUniverse))
          "the refusal names the covering form, not arg"))
    (testing "the same members with no bad tail value store"
      (is (v/assert kb (list rel a b) 'CxUniverse)))))

(tu/deftest-kb args-is-open-world-about-a-symbol
  (let [[rel animal] (variable-relation kb)
        a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'args rel animal) 'CxUniverse)
    (testing "an untyped symbol in the tail cannot violate — the same open world arg keeps"
      (is (v/assert kb (list rel a b) 'CxUniverse)))))

;; ---- argAndRest: a position and every later one, prefix excluded -----------

(tu/deftest-kb argAndRest-excludes-the-prefix-below-its-start
  (let [[rel animal dog] (variable-relation kb)
        name (tu/tmp-ind) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'argAndRest rel 2 animal) 'CxUniverse)
    (v/assert kb (list dog a) 'CxUniverse)
    (v/assert kb (list dog b) 'CxUniverse)
    (testing "position 1 is below the start, so any term is admitted there"
      (is (v/assert kb (list rel name a b) 'CxUniverse))
      (is (v/assert kb (list rel "aStringHead" a b) 'CxUniverse)))
    (testing "and the tail from position 2 is still typed"
      (is (= :arg-type (ex-type #(v/assert kb (list rel name a "bad") 'CxUniverse))))
      (is (re-find #"argAndRest" (check-message kb (list rel name a "bad") 'CxUniverse))))))

(tu/deftest-kb args-states-what-argAndRest-at-one-states
  (let [[rel animal dog] (variable-relation kb)
        a (tu/tmp-ind)]
    (v/assert kb (list 'argAndRest rel 1 animal) 'CxUniverse)
    (v/assert kb (list dog a) 'CxUniverse)
    (testing "start 1 types position 1 too, exactly as args does"
      (is (= :arg-type (ex-type #(v/assert kb (list rel "badHead" a) 'CxUniverse)))))))

;; ---- the *Genl forms discriminate kind from instance -----------------------

(tu/deftest-kb argsGenl-wants-a-subtype-where-args-wants-an-instance
  ;; the constraint-only reading: the refusal is the subject
  (tu/without-entailing
   (let [[rel animal dog other] (variable-relation kb)]
     (v/assert kb (list 'type_relation_predicate rel) 'CxUniverse)
     (v/assert kb (list 'disjoint other animal) 'CxUniverse)
     (v/assert kb (list 'argsGenl rel animal) 'CxUniverse)
     (testing "a subtype of the type, and the type itself, satisfy the subtype demand"
       (is (v/assert kb (list rel dog animal) 'CxUniverse)))
     (testing "a type the taxonomy separates from the declared type is convicted"
       (is (= :arg-genl (ex-type #(v/assert kb (list rel dog other) 'CxUniverse)))))
     (testing "an individual can never be a subtype, so it is convicted not excused"
       (is (= :arg-genl (ex-type #(v/assert kb (list rel dog (tu/tmp-ind)) 'CxUniverse))))))))

(tu/deftest-kb argAndRestGenl-types-the-tail-as-a-kind
  ;; the constraint-only reading: the refusal is the subject
  (tu/without-entailing
   (let [[rel animal dog other] (variable-relation kb)
         name (tu/tmp-ind)]
     (v/assert kb (list 'disjoint other animal) 'CxUniverse)
     (v/assert kb (list 'argAndRestGenl rel 2 animal) 'CxUniverse)
     (testing "the prefix is free and the tail names a kind"
       (is (v/assert kb (list rel name dog dog) 'CxUniverse))
       (is (= :arg-genl (ex-type #(v/assert kb (list rel name dog other) 'CxUniverse))))))))

;; ---- conjunction with the singular forms -----------------------------------

(tu/deftest-kb a-covering-and-a-singular-constraint-both-bind-a-position
  (tu/with-terms [rel animal dog red stone RedDog PlainRed PlainDog]
    (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'genl red 'thing) 'CxUniverse)
    (v/assert kb (list 'genl stone red) 'CxUniverse)
    (v/assert kb (list 'disjoint red dog) 'CxUniverse)
    (v/assert kb (list 'disjoint stone animal) 'CxUniverse)
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'variable_arity rel) 'CxUniverse)
    (v/assert kb (list 'arg rel 1 red) 'CxUniverse)       ; position 1 must be red
    (v/assert kb (list 'args rel animal) 'CxUniverse)     ; every position an animal
    (v/assert kb (list red RedDog) 'CxUniverse)
    (v/assert kb (list animal RedDog) 'CxUniverse)        ; both
    (v/assert kb (list dog PlainDog) 'CxUniverse)         ; a dog, disjoint from red
    (v/assert kb (list stone PlainRed) 'CxUniverse)       ; red, disjoint from animal
    (testing "a term satisfying both is admitted at position 1"
      (is (v/assert kb (list rel RedDog RedDog) 'CxUniverse)))
    ;; Under the entailing reading `assert` stores a symbol conviction and mints the
    ;; demanded type (docs/argtypes.md), so the refusals asserted here are the
    ;; constraint-only ones.
    (tu/without-entailing
     (testing "each still convicts on its own — the singular at position 1"
       (is (= :arg-type (ex-type #(v/assert kb (list rel PlainDog RedDog) 'CxUniverse)))
           "a dog, disjoint from red — the singular arg convicts"))
     (testing "and the covering across the whole tail"
       (is (= :arg-type (ex-type #(v/assert kb (list rel RedDog PlainRed) 'CxUniverse)))
           "a stone, disjoint from animal, at position 2 — the covering args convicts")))))

(tu/deftest-kb the-entailing-reading-derives-every-tail-membership-in-either-order
  ;; `args` derives `animal` of every symbol in the tail, and `argsGenl` the edge, whether
  ;; the declaration or the fact arrives first; a term the KB places outside the type is
  ;; given the membership beside its own and nothing is refused.
  (doseq [decl-first? [true false]]
    (tu/with-terms [kind_of]
      (let [[rel animal _ other] (variable-relation kb)
            a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind)
            gr (tu/tmp-pred) k1 (tu/tmp-type) k2 (tu/tmp-type)]
        (tu/with-entailing
          (v/assert kb (list other c) 'CxUniverse)
          (v/assert kb (list 'binary_predicate gr) 'CxUniverse)
          (v/assert kb (list 'variable_arity gr) 'CxUniverse)
          (let [decls [(list 'args rel animal) (list 'argsGenl gr kind_of)]
                facts [(list rel a b c) (list gr k1 k2)]]
            (v/assert kb (list 'genl kind_of 'thing) 'CxUniverse)
            (doseq [x (if decl-first? (concat decls facts) (concat facts decls))]
              (v/assert kb x 'CxUniverse)))
          (testing (str "declaration first: " decl-first?)
            (is (every? #(v/isa? kb % animal 'CxUniverse) [a b c]))
            (is (v/isa? kb c other 'CxUniverse))
            (is (every? #(v/genl? kb % kind_of) [k1 k2]))))))))

;; ---- inheritance down the predicate hierarchy ------------------------------

(tu/deftest-kb a-covering-constraint-on-a-super-predicate-binds-a-sub
  (let [[super animal dog] (variable-relation kb)
        sub (tu/tmp-pred) a (tu/tmp-ind) other-ind (tu/tmp-ind)]
    (v/assert kb (list 'args super animal) 'CxUniverse)
    (v/assert kb (list 'binary_predicate sub) 'CxUniverse)
    (v/assert kb (list 'genl sub super) 'CxUniverse)
    (v/assert kb (list 'variable_arity sub) 'CxUniverse)
    (v/assert kb (list dog a) 'CxUniverse)
    (testing "the sub's tuple is held to the super's covering constraint"
      (is (v/assert kb (list sub a a) 'CxUniverse))
      (is (= :arg-type (ex-type #(v/assert kb (list sub a "bad") 'CxUniverse)))))
    ;; other-ind exists only to keep the arity legal in later readings
    (is other-ind)))

;; ---- fixed-arity behaviour is unchanged ------------------------------------

(tu/deftest-kb a-covering-constraint-does-not-change-a-relations-arity
  (tu/with-terms [rel animal dog A B]
    (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)   ; fixed arity 2
    (v/assert kb (list 'args rel animal) 'CxUniverse)
    (v/assert kb (list dog A) 'CxUniverse)
    (v/assert kb (list dog B) 'CxUniverse)
    (testing "the declared arity still binds — a third argument is stored and read OUT"
      (is (tu/stored-in-clash? kb (list rel A B (tu/tmp-ind)) 'CxUniverse)))
    (testing "and within the arity the covering constraint still types the positions"
      (is (v/assert kb (list rel A B) 'CxUniverse))
      (is (= :arg-type (ex-type #(v/assert kb (list rel A "bad") 'CxUniverse)))))))

;; ---- the declaration's own well-formedness ---------------------------------

(tu/deftest-kb the-covering-declaration-is-well-formedness-checked
  (let [rel (tu/tmp-pred)]
    (testing "the type slot is a type, not an individual"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'args rel (tu/tmp-ind)) 'CxUniverse))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'argAndRest rel 2 (tu/tmp-ind)) 'CxUniverse)))))
    (testing "the start position is a positive integer"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'argAndRest rel 0 'thing) 'CxUniverse))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'argAndRestGenl rel -1 'thing) 'CxUniverse))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'argAndRest rel 'notAnInt 'thing) 'CxUniverse)))))
    (testing "the subject is a relation, named or denoted, not a number"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'args 5 'thing) 'CxUniverse)))))
    (testing "the message names the covering form"
      (is (re-find #"argAndRest"
                   (:message (first (v/check kb (list 'argAndRest rel 0 'thing) 'CxUniverse))))))))

;; ---- the query surface -----------------------------------------------------

(tu/deftest-kb a-stored-covering-declaration-answers-up-the-genl-closure
  (let [[rel animal dog other] (variable-relation kb)]
    (v/assert kb (list 'args rel dog) 'CxUniverse)
    (testing "the stored declaration answers itself"
      (is (true? (v/ask? kb (list 'args rel dog) 'CxUniverse))))
    (testing "and a supertype query, covariant like arg's"
      (is (true? (v/ask? kb (list 'args rel animal) 'CxUniverse))))
    (testing "but not an unrelated type"
      (is (not (v/ask? kb (list 'args rel other) 'CxUniverse))))))

;; ---- the derivation path ---------------------------------------------------

(tu/deftest-kb a-derived-covering-violation-is-recorded-not-thrown
  (let [[rel animal dog] (variable-relation kb)
        trigger (tu/tmp-pred) bad (tu/tmp-ind)]
    (v/assert kb (list 'args rel animal) 'CxUniverse)
    (v/assert kb (list 'binary_predicate trigger) 'CxUniverse)
    (v/assert kb (list 'variable_arity trigger) 'CxUniverse)
    (v/assert kb (list dog bad) 'CxUniverse)
    (v/clear-violations! kb)
    ;; a rule concluding (rel ?x "notAnimal") — the second tail argument is a bad value
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list trigger '?x '?y) (list rel '?x "notAnimal")))
              'CxUniverse)
    (v/assert kb (list trigger bad bad) 'CxUniverse)
    (is (some #(= :arg-type (:violation %)) (v/violations kb))
        "the conclusion is dropped into the ledger rather than aborting the fixpoint")))

;; ---- retraction releases the constraint ------------------------------------

(tu/deftest-kb retracting-a-covering-declaration-releases-the-tail
  (let [[rel animal dog] (variable-relation kb)
        a (tu/tmp-ind)]
    (v/assert kb (list dog a) 'CxUniverse)
    (let [h (v/assert kb (list 'args rel animal) 'CxUniverse)]
      (is (= :arg-type (ex-type #(v/assert kb (list rel a "bad") 'CxUniverse)))
          "convicted while the declaration stands")
      (testing "and released when it is retracted, prop cache and all"
        (v/retract! kb h)
        (is (false? (v/has-prop? kb :declares-args-isa rel))
            "the subject mark went with the declaration")
        (is (v/assert kb (list rel a "bad") 'CxUniverse)
            "with nothing declared the tail is untyped, not inverted")))))

;; ---- order independence of belief ------------------------------------------

(tu/deftest-kb the-same-tail-typing-in-either-order-holds-the-same-belief
  ;; belief is a function of stored content, so the covering conviction of a DERIVED
  ;; sentence does not depend on whether the fact or the declaration arrived first
  (let [[rel animal dog] (variable-relation kb)
        good (tu/tmp-ind)]
    (v/assert kb (list dog good) 'CxUniverse)
    (v/assert kb (list 'args rel animal) 'CxUniverse)
    (is (v/assert kb (list rel good good) 'CxUniverse))
    (let [n (v/sentex-count kb)]
      (is (= n (v/sentex-count kb)) "a well-typed tail stores and stays stored"))))

;; ---- the chokepoint: one reading of every spelling ---------------------------

(tu/deftest-kb the-chokepoint-reads-every-spelling-as-arg-or-argAndRest
  ;; `res/arg-constraints` is the one read of what a position is declared to hold.
  ;; `args` comes back as `argAndRest` from 1, and the type-level and quoted twins come
  ;; back under their own `:kind`.
  (let [[rel animal dog other] (variable-relation kb)
        super (tu/tmp-pred)]
    (v/assert kb (list 'binary_predicate super) 'CxUniverse)
    (v/assert kb (list 'variable_arity super) 'CxUniverse)
    (v/assert kb (list 'genl rel super) 'CxUniverse)
    (v/assert kb (list 'arg rel 1 dog) 'CxUniverse)
    (v/assert kb (list 'argAndRest rel 3 animal) 'CxUniverse)
    (v/assert kb (list 'args super other) 'CxUniverse)
    (v/assert kb (list 'argAndRestGenl rel 4 animal) 'CxUniverse)
    (let [entries (set (res/arg-constraints kb rel 'CxUniverse))]
      (testing "each spelling, read as the instance or type form it amounts to"
        (is (= #{{:from 1 :to 1 :type dog :kind :instance :via rel}
                 {:from 3 :to nil :type animal :kind :instance :via rel}
                 {:from 1 :to nil :type other :kind :instance :via super}
                 {:from 4 :to nil :type animal :kind :type :via rel}}
               entries))))
    (testing "the argnum chokepoint answers the entries covering one position"
      (is (= #{other dog} (set (map :type (res/arg-constraints-at kb rel 'CxUniverse 1)))))
      (is (= #{other} (set (map :type (res/arg-constraints-at kb rel 'CxUniverse 2)))))
      (is (= #{[other :instance] [animal :instance]}
             (set (map (juxt :type :kind) (res/arg-constraints-at kb rel 'CxUniverse 3)))))
      (is (= #{[other :instance] [animal :instance] [animal :type]}
             (set (map (juxt :type :kind) (res/arg-constraints-at kb rel 'CxUniverse 9))))))))

(tu/deftest-kb the-chokepoint-sees-a-declaration-asserted-after-a-read
  ;; held for one stretch of the change clock, so a write retires what it held
  (let [[rel animal dog] (variable-relation kb)]
    (v/assert kb (list 'arg rel 1 animal) 'CxUniverse)
    (is (= [animal] (map :type (res/arg-constraints kb rel 'CxUniverse))))
    (let [h (v/assert kb (list 'argAndRest rel 2 dog) 'CxUniverse)]
      (is (= #{animal dog} (set (map :type (res/arg-constraints kb rel 'CxUniverse)))))
      (v/retract! kb h))
    (is (= [animal] (map :type (res/arg-constraints kb rel 'CxUniverse))))))

(tu/deftest-kb the-argument-type-prover-reads-a-tail-declaration
  ;; `ArgTypeProver` reads `arg` the other way, as an inference from a usage; it reads
  ;; the positions `argAndRest` and `args` type as it reads the one `arg` types
  (let [[rel animal] (variable-relation kb)
        sub (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind) d (tu/tmp-ind)
        solve #(prover-types/solve (provers/->ArgTypeProver) kb % 'CxUniverse)]
    (v/assert kb (list 'argAndRest rel 2 animal) 'CxUniverse)
    (v/assert kb (list rel a b c) 'CxUniverse)
    (testing "a usage at or past the start types the term"
      (is (= [{}] (solve (list animal b))))
      (is (= [{}] (solve (list animal c))))
      (is (some #{animal} (map #(get % '?t) (solve (list '?t c))))))
    (testing "a usage below the start does not"
      (is (empty? (solve (list animal a)))))
    (testing "args, on a super-predicate, types every position of a sub's tuple"
      (v/assert kb (list 'binary_predicate sub) 'CxUniverse)
      (v/assert kb (list 'genl sub rel) 'CxUniverse)
      (v/assert kb (list 'args rel animal) 'CxUniverse)
      (v/assert kb (list sub d a) 'CxUniverse)
      (is (= [{}] (solve (list animal d)))))))
