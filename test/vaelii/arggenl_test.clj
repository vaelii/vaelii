;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arggenl-test
  "`genlArg` — the argument constraint one level up.  Where `arg` asks an argument
  to be an *instance* of a type, `genlArg` asks it to be a *subtype*, which is what a
  `type_relation_predicate` wants: its arguments name kinds, not things.

  Plus the checks over the declarations themselves — arity, and the two ways an
  `arg` / `genlArg` can contradict what the KB already says about its predicate.
  Declaring *both* of them on one position is not one of those ways: they ask
  different questions about the slot and a type answers both.

  And what each reads an argument's type *off*: a symbol's memberships, a literal's EDN
  kind, and — for a function application, which has neither — its function's declared
  result."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw.

  The paths below throw five distinguishable types — `:arg-genl` for the subtype
  constraint, `:arg-type` for the instance one, `:arity` and `:arg-position` for the
  declarations, `:functional` for a second arity value — and a bare
  `(thrown? ExceptionInfo …)` passes for every one of them alike.  An `genlArg` check
  collapsing into a naming refusal is exactly the regression a file full of those would
  stay green through, so each refusal here names the one it expects."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- type-relation
  "A type-level relation over kinds of `root`, plus the kinds themselves.
  Returns `[rel sub other root]`."
  [kb]
  (let [rel (tu/tmp-pred) root (tu/tmp-type) sub (tu/tmp-type) other (tu/tmp-type)]
    (v/assert kb (list 'genl root 'thing) 'CxUniverse)
    (v/assert kb (list 'genl sub root) 'CxUniverse)
    (v/assert kb (list 'genl other 'thing) 'CxUniverse)   ; a type, but not under root
    (v/assert kb (list 'genlArg rel 1 root) 'CxUniverse)
    [rel sub other root]))

(tu/deftest-kb a-subtype-satisfies-genlArg-and-a-sibling-does-not
  (let [[rel sub other root] (type-relation kb)]
    (testing "a subtype of the constraint type is what the position wants"
      (is (v/assert kb (list rel sub (tu/tmp-type)) 'CxUniverse)))
    (testing "the constraint type itself satisfies it — genl is reflexive"
      (is (v/assert kb (list rel root (tu/tmp-type)) 'CxUniverse)))
    (testing "a type outside the constraint's down-closure does not"
      (is (= :arg-genl (ex-type #(v/assert kb (list rel other (tu/tmp-type)) 'CxUniverse)))))))

(tu/deftest-kb genlArg-wants-a-subtype-where-arg-wants-an-instance
  ;; the whole point of having both: the same type symbol passes one and fails the other
  (let [[rel sub] (type-relation kb)
        instRel (tu/tmp-pred) root2 (tu/tmp-type)]
    (v/assert kb (list 'genl root2 'thing) 'CxUniverse)
    (v/assert kb (list 'genl sub root2) 'CxUniverse)
    (v/assert kb (list 'arg instRel 1 root2) 'CxUniverse)
    ;; a type symbol comes within arg's reach only once it carries a membership of
    ;; its own reaching `thing` — which is what the starter's (unary_predicate t) batch
    ;; does for every type.  Without one the open-world exemption applies and there is
    ;; nothing to convict, so the test states it rather than assuming a loaded KB.
    (let [meta (tu/tmp-type)]
      (v/assert kb (list 'genl meta 'thing) 'CxUniverse)
      (v/assert kb (list meta sub) 'CxUniverse))
    (testing "the kind satisfies genlArg"
      (is (v/assert kb (list rel sub (tu/tmp-type)) 'CxUniverse)))
    (testing "and fails arg, which wants one of its instances"
      (is (= :arg-type (ex-type #(v/assert kb (list instRel sub (tu/tmp-ind)) 'CxUniverse)))))
    (testing "an instance of the kind is what arg wanted"
      (let [x (tu/tmp-ind)]
        (v/assert kb (list sub x) 'CxUniverse)
        (is (v/assert kb (list instRel x (tu/tmp-ind)) 'CxUniverse))))))

(tu/deftest-kb an-unplaced-type-is-excused-but-an-individual-is-not
  (let [[rel] (type-relation kb)]
    (testing "open-world: a term with no place in the hierarchy yet cannot violate"
      (is (v/assert kb (list rel (tu/tmp-type) (tu/tmp-type)) 'CxUniverse)))
    (testing "an individual can never acquire genl edges, so it is convicted not excused"
      (is (= :arg-genl (ex-type #(v/assert kb (list rel (tu/tmp-ind) (tu/tmp-type)) 'CxUniverse)))))))

(tu/deftest-kb genlArg-is-well-formedness-checked-like-arg
  (let [rel (tu/tmp-pred)]
    (testing "the type slot is a type, not an individual"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'genlArg rel 1 (tu/tmp-ind)) 'CxUniverse)))))
    (testing "the position is a positive integer"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'genlArg rel 0 'thing) 'CxUniverse)))))
    (testing "the message names genlArg, not arg"
      (is (re-find #"genlArg"
                   (:message (first (v/check kb (list 'genlArg rel 0 'thing)
                                             'CxUniverse))))))))

(tu/deftest-kb a-derived-genlArg-violation-is-recorded-not-thrown
  ;; the derivation path must not abort a fixpoint, so it drops and ledgers instead
  (let [[rel _ other] (type-relation kb)
        trigger (tu/tmp-pred)]
    (v/clear-violations! kb)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list trigger '?x) (list rel '?x other)))
              'CxUniverse)
    (v/assert kb (list trigger other) 'CxUniverse)
    (is (some #(= :arg-genl (:violation %)) (v/violations kb))
        "the conclusion is dropped into the ledger")))

;; ---- the constraint declarations, checked against each other -------------

(tu/deftest-kb a-constraint-on-a-position-the-predicate-lacks-is-refused
  (let [rel (tu/tmp-pred)]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (testing "a declared position is fine"
      (is (v/assert kb (list 'arg rel 2 'thing) 'CxUniverse)))
    (testing "one past the declared arity would never fire, so it is refused"
      (is (= :arg-position (ex-type #(v/assert kb (list 'arg rel 5 'thing) 'CxUniverse))))
      (is (= :arg-position (ex-type #(v/assert kb (list 'genlArg rel 5 'thing) 'CxUniverse)))))
    (testing "open-world: an undeclared predicate takes any position"
      (is (v/assert kb (list 'arg (tu/tmp-pred) 9 'thing) 'CxUniverse)))))

(tu/deftest-kb both-constraints-on-one-position-narrow-it-rather-than-emptying-it
  ;; The two constraints ask different questions about the same slot — one *what kind
  ;; of thing* it holds, one *where in the hierarchy* — and a type answers both.  This
  ;; is how an imported ontology routinely declares a type-valued position, so refusing
  ;; the pair on the grounds that nothing satisfies both would be refusing knowledge on
  ;; a premise that is false.
  (tu/with-terms [rel a_collection an_animal a_dog Rex]
    (v/assert kb (list 'genl a_collection 'thing) 'CxUniverse)
    (v/assert kb (list 'genl an_animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl a_dog an_animal) 'CxUniverse)
    (v/assert kb (list a_collection a_dog) 'CxUniverse)  ; a_dog *is* a collection

    (testing "both may be declared of one position"
      (is (v/assert kb (list 'arg rel 1 a_collection) 'CxUniverse))
      (is (v/assert kb (list 'genlArg rel 1 an_animal) 'CxUniverse)))

    (testing "and a term satisfying both is admitted — an instance of the one, a subtype of the other"
      (is (v/assert kb (list rel a_dog (tu/tmp-ind)) 'CxUniverse)))

    (testing "each is still enforced on its own"
      (tu/with-terms [a_plant]
        (v/assert kb (list 'genl a_plant 'thing) 'CxUniverse)
        (v/assert kb (list a_collection a_plant) 'CxUniverse)
        (is (= :arg-genl (ex-type #(v/assert kb (list rel a_plant (tu/tmp-ind)) 'CxUniverse)))
            "a collection, but not a kind of animal — genlArg convicts"))
      (is (= :arg-genl (ex-type #(v/assert kb (list rel Rex (tu/tmp-ind)) 'CxUniverse)))
          "an individual can never be a subtype, so it is convicted rather than excused"))))

(tu/deftest-kb the-constraint-must-agree-with-the-declared-relation-kind
  (let [instRel (tu/tmp-pred) typeRel (tu/tmp-pred)]
    (v/assert kb (list 'instance_relation_predicate instRel) 'CxUniverse)
    (v/assert kb (list 'type_relation_predicate typeRel) 'CxUniverse)
    (testing "an instance-level relation takes arg"
      (is (v/assert kb (list 'arg instRel 1 'thing) 'CxUniverse))
      (is (= :arg-constraint-kind (ex-type #(v/assert kb (list 'genlArg instRel 2 'thing) 'CxUniverse)))))
    (testing "a type-level relation takes genlArg"
      (is (v/assert kb (list 'genlArg typeRel 1 'thing) 'CxUniverse))
      (is (= :arg-constraint-kind (ex-type #(v/assert kb (list 'arg typeRel 2 'thing) 'CxUniverse)))))
    (testing "an unclassified relation takes either"
      (let [rel (tu/tmp-pred)]
        (is (v/assert kb (list 'arg rel 1 'thing) 'CxUniverse))
        (is (v/assert kb (list 'genlArg rel 2 'thing) 'CxUniverse))))))

(tu/deftest-kb arity-is-functional-so-a-second-value-is-refused
  ;; the declaration ships in CxCore; this KB is empty, so it states it — that
  ;; the shipped vocabulary carries it is core-context-test's assertion
  (let [rel (tu/tmp-pred)]
    (v/assert kb '(functional arity) 'CxUniverse)
    (v/assert kb (list 'arity rel 2) 'CxUniverse)
    (testing "restating the same arity is a no-op, not a clash"
      (is (v/assert kb (list 'arity rel 2) 'CxUniverse)))
    (testing "a different arity for the same predicate is a functional violation"
      (is (= :functional (ex-type #(v/assert kb (list 'arity rel 7) 'CxUniverse)))))))

(tu/deftest-kb a-sentence-must-match-its-predicates-declared-arity
  (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (testing "the declared arity stores"
      (is (v/assert kb (list rel a b) 'CxUniverse)))
    (testing "too many arguments, and too few, are both refused"
      (is (= :arity (ex-type #(v/assert kb (list rel a b (tu/tmp-ind)) 'CxUniverse))))
      (is (= :arity (ex-type #(v/assert kb (list rel a) 'CxUniverse)))))
    (testing "open-world: an undeclared predicate takes any arity"
      (let [undeclared (tu/tmp-pred)]
        (is (v/assert kb (list undeclared a) 'CxUniverse))
        (is (v/assert kb (list undeclared a b) 'CxUniverse))))))

(tu/deftest-kb the-arity-declaration-can-come-from-either-spelling
  ;; (arity P N) and the N-ary predicate type derive each other, so either alone binds
  (let [byArity (tu/tmp-pred) byType (tu/tmp-pred) a (tu/tmp-ind)]
    (v/assert kb (list 'arity byArity 1) 'CxUniverse)
    (v/assert kb (list 'unary_predicate byType) 'CxUniverse)
    (is (v/assert kb (list byArity a) 'CxUniverse))
    (is (v/assert kb (list byType a) 'CxUniverse))
    (is (= :arity (ex-type #(v/assert kb (list byArity a (tu/tmp-ind)) 'CxUniverse))))
    (is (= :arity (ex-type #(v/assert kb (list byType a (tu/tmp-ind)) 'CxUniverse))))))

(tu/deftest-kb the-arity-declaration-is-cached-and-follows-its-sentex
  ;; `(arity P n)` is read on every assertion, so it is cached in the taxonomy beside
  ;; `transitive` and `inverse` rather than re-queried.  A cache is only right if it
  ;; goes when its sentex does — the same discipline every other declaration keeps.
  (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (let [h (v/assert kb (list 'arity rel 2) 'CxUniverse)]
      (is (= 2 (tax/declared-arity (:taxonomy kb) rel)) "cached on assert")
      (is (= :arity (ex-type #(v/assert kb (list rel a) 'CxUniverse))))
      (testing "and retracting the declaration takes the constraint with it"
        (v/retract! kb h)
        (is (nil? (tax/declared-arity (:taxonomy kb) rel)))
        (is (v/assert kb (list rel a) 'CxUniverse))
        (is (v/assert kb (list rel a b) 'CxUniverse)
            "the arity the declaration named is admitted too — with nothing declared
             the check is released, not inverted")))
    (testing "and a rebuild from the records agrees with the live cache"
      (let [h2 (v/assert kb (list 'arity (tu/tmp-pred) 3) 'CxUniverse)
            sx (v/sentex kb h2)
            p2 (second (:sentence sx))]
        (v/recover kb)
        (is (= 3 (tax/declared-arity (:taxonomy kb) p2))
            "recover replays the declaration into the cache")))))

(tu/deftest-kb a-rebuild-clears-the-arity-cache-before-replaying-it
  ;; `recover` merges into what it clears, so a cache it forgets to clear can only ever
  ;; *grow*: an entry whose sentex is gone would outlive the rebuild meant to re-derive
  ;; it.  The same rule the other seven caches keep.
  ;; The scenario needs the live cache to hold an entry whose record is gone, which a
  ;; retraction never produces (it drops both).  `clear!` does exactly that — it wipes
  ;; the stores and deliberately leaves the in-memory caches alone — so it is the shape
  ;; a reset-and-reload takes, and the one that catches a cache `recover` forgot.
  (tu/with-cleared-kb [kb2 tu/fresh]
    (let [rel (tu/tmp-pred) a (tu/tmp-ind)]
      (v/assert kb2 (list 'arity rel 2) 'CxUniverse)
      (is (= 2 (tax/declared-arity (:taxonomy kb2) rel)))
      (v/clear! kb2)
      (v/recover kb2)
      (is (nil? (tax/declared-arity (:taxonomy kb2) rel))
          "the rebuild re-derives from the records, it does not top up")
      (is (v/assert kb2 (list rel a) 'CxUniverse)
          "and the constraint went with the declaration"))))

(tu/deftest-kb the-arity-a-reader-sees-is-the-one-that-binds-it
  ;; Two contexts declaring different arities: each reader that sees one sees one
  ;; answer.  Uniqueness is asked of the visible declarations, so a declaration a
  ;; reader cannot see neither binds it nor suppresses the one it can.
  (tu/with-terms [CxLeft CxRight CxBoth]
    (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
      (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxBoth CxLeft) 'CxUniverse)
      (v/assert kb (list 'genlCx CxBoth CxRight) 'CxUniverse)
      (v/assert kb (list 'arity rel 2) CxLeft)
      (v/assert kb (list 'arity rel 3) CxRight)
      (let [tax (:taxonomy kb)]
        (is (= 2 (tax/declared-arity tax rel CxLeft)) "sees only the binary one")
        (is (= 3 (tax/declared-arity tax rel CxRight)) "sees only the ternary one")
        (is (nil? (tax/declared-arity tax rel CxBoth))
            "sees both, so has no settled answer")
        (is (nil? (tax/declared-arity tax rel)) "and unscoped is the same"))
      (testing "and each reader is bound by what it sees"
        (is (= :arity (ex-type #(v/assert kb (list rel a) CxLeft))))
        (is (v/assert kb (list rel a b) CxLeft))
        (is (v/assert kb (list rel a b) CxBoth) "unsettled constrains nothing")))))

(tu/deftest-kb two-arities-for-one-predicate-constrain-nothing
  ;; The cache holds what it was told, and it was told two different things.  Refusing
  ;; on whichever was found first would be arbitrary — the same open-world stance the
  ;; check takes toward a predicate nobody has declared at all.  (An ordinary KB never
  ;; gets here: `(functional arity)` merges the two values instead, and CxCore
  ;; ships that declaration.  A KB without it, or an import that stored both, does.)
  (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'arity rel 2) 'CxUniverse)
    (v/assert kb (list 'arity rel 3) 'CxUniverse)
    (is (nil? (tax/declared-arity (:taxonomy kb) rel))
        "unsettled, which is not the same as undeclared but constrains the same")
    (is (v/assert kb (list rel a b) 'CxUniverse))
    (is (v/assert kb (list rel a b (tu/tmp-ind)) 'CxUniverse))
    (testing "and dropping one of them settles it again"
      (v/retract! kb (v/handle-of kb (list 'arity rel 3) 'CxUniverse))
      (is (= 2 (tax/declared-arity (:taxonomy kb) rel)))
      (is (= :arity (ex-type #(v/assert kb (list rel a) 'CxUniverse)))))))

(tu/deftest-kb a-variableArity-predicate-is-exempt
  ;; lessThan has a binary floor and reads a chain of any length; the declaration says so
  (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (is (= :arity (ex-type #(v/assert kb (list rel a b (tu/tmp-ind)) 'CxUniverse))))
    (v/assert kb (list 'variable_arity rel) 'CxUniverse)
    (testing "declaring it variable arity releases the check"
      (is (v/assert kb (list rel a b (tu/tmp-ind)) 'CxUniverse)))))

(tu/deftest-kb a-variableArity-predicate-takes-a-constraint-past-its-declared-length
  ;; One release, so the entry point owes the same answer twice.  A predicate reading a chain of
  ;; any length has the arguments past its declared number, and a constraint on one of them
  ;; fires on exactly the tuples that reach it — so refusing the declaration while storing
  ;; the three-argument fact leaves the third argument untypeable in a KB that admits it.
  (tu/with-terms [chainOf a_type b_type A B C Odd]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'genl b_type 'thing) 'CxUniverse)
    (v/assert kb (list 'binary_predicate chainOf) 'CxUniverse)
    (is (= :arg-position
           (ex-type #(v/assert kb (list 'arg chainOf 3 a_type) 'CxUniverse)))
        "binary and nothing else, so there is no third argument to constrain")
    (v/assert kb (list 'variable_arity chainOf) 'CxUniverse)
    (testing "the mark releases the declaration exactly as it releases the tuple"
      (is (v/assert kb (list 'arg chainOf 3 a_type) 'CxUniverse))
      (is (v/assert kb (list 'genlArg chainOf 4 'thing) 'CxUniverse)))
    (testing "both of interArg's positions are released, not only the first"
      (is (v/assert kb (list 'interArg chainOf 1 a_type 5 a_type) 'CxUniverse)))
    (testing "and the constraint is live on the tuple that reaches the position"
      (v/assert kb (list a_type C) 'CxUniverse)
      (v/assert kb (list b_type Odd) 'CxUniverse)          ; placed, but not an a_type
      (is (v/assert kb (list chainOf A B C) 'CxUniverse))
      (is (= :arg-type (ex-type #(v/assert kb (list chainOf A B Odd) 'CxUniverse)))
          "argument 3 is enforced where the tuple has one, which is what makes the
           declaration worth admitting"))))

(tu/deftest-kb a-variableArity-sub-takes-a-constraint-past-the-length-above-it
  ;; The inherited route into the same arm, and the mark sits where the inheritance never
  ;; looks: `inherited-arity` asks the release of the *supers*, so a sub carrying it still
  ;; reads their length — and only the arm's own reading of the predicate's memberships
  ;; releases the position.
  (tu/with-terms [chainOf subChainOf a_type A B C]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'binary_predicate chainOf) 'CxUniverse)
    (v/assert kb (list 'genl subChainOf chainOf) 'CxUniverse)
    (is (= :arg-position
           (ex-type #(v/assert kb (list 'arg subChainOf 3 a_type) 'CxUniverse)))
        "subChainOf declares no length, so it takes two arguments through chainOf")
    (v/assert kb (list 'variable_arity subChainOf) 'CxUniverse)
    (testing "the mark on the sub releases what the super bound it to"
      (is (v/assert kb (list 'arg subChainOf 3 a_type) 'CxUniverse))
      (v/assert kb (list a_type C) 'CxUniverse)
      (is (v/assert kb (list subChainOf A B C) 'CxUniverse)
          "the same release the tuple already had"))
    (testing "and the super it inherits from keeps its own length"
      (is (= :arg-position
             (ex-type #(v/assert kb (list 'arg chainOf 3 a_type) 'CxUniverse)))
          "chainOf is binary, whatever mark its sub-predicates carry"))))

;; ---- the global/scoped split in the conviction ---------------------------
;; `genls-problem` runs three probes: a **global** individual floor (could the
;; argument ever be a type?), a **scoped** open-world floor (does the writer see
;; any evidence at all?), and the scoped subtype test.  The middle one is what
;; keeps a NAF check from convicting harder the less a context sees: an imported
;; reified NAT's minting edges land in CxUniverse, and a writer whose ancestor set does not
;; reach them must excuse, not convict.

(tu/deftest-kb an-argument-whose-edges-are-out-of-sight-is-excused-not-convicted
  (let [rel (tu/tmp-pred) root (tu/tmp-type) kind (tu/tmp-type)
        reified (tu/tmp-ind) plain (tu/tmp-ind)
        ctx (tu/tmp-ctx)]
    ;; ctx is deliberately unwired: it cannot see CxUniverse
    (v/assert kb (list 'genl root 'thing) ctx)
    (v/assert kb (list 'genlArg rel 1 root) ctx)
    ;; a reified NAT-shaped constant minted with real genl edges into CxUniverse —
    ;; the raw writer stands in for nat/mint-nat!, whose edges are exactly this
    (tax/add-genl (:taxonomy kb) reified root 999901 'CxUniverse)
    (testing "globally in the hierarchy, invisibly from ctx: open world excuses"
      (is (v/assert kb (list rel reified (tu/tmp-type)) ctx)))
    (testing "a plain individual with no edges anywhere is still convicted"
      (is (= :arg-genl (ex-type #(v/assert kb (list rel plain (tu/tmp-type)) ctx)))))
    (testing "visible evidence reaching the wrong place still convicts"
      (v/assert kb (list 'genl kind 'thing) ctx)     ; visible, but not under root
      (is (= :arg-genl (ex-type #(v/assert kb (list rel kind (tu/tmp-type)) ctx)))))
    (tax/del-genl! (:taxonomy kb) reified root 999901)))

;; ---- a literal is typed by what it is ------------------------------------
;; `arg` is open-world about a **symbol** — an untyped one violates nothing — and closed
;; about a **literal**, whose kind `checks/value-kind` reads straight off its syntax.
;; The kinds live in the genl lattice (CxCore) so the comparison is an ordinary one;
;; these assert the edges they lean on rather than loading the schema, so what the check
;; actually depends on is visible in the test.

(tu/deftest-kb a-literal-is-checked-against-its-kind-and-a-symbol-is-not
  (let [p (tu/tmp-pred) t (tu/tmp-type)]
    (v/assert kb '(genl string thing) 'CxUniverse)
    (v/assert kb (list 'genl t 'thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate p) 'CxUniverse)
    (v/assert kb (list 'arg p 1 t) 'CxUniverse)
    (testing "a string is not a t, and nobody had to assert a membership to say so"
      (is (= :arg-type (ex-type #(v/assert kb (list p "Bob") 'CxUniverse)))))
    (testing "a symbol nothing types is exempt — open-world, and unchanged"
      (is (v/assert kb (list p (tu/tmp-ind)) 'CxUniverse)))
    (testing "and a literal the type does reach is admitted"
      (v/assert kb (list 'genl 'string t) 'CxUniverse)
      (is (v/assert kb (list p "Bob") 'CxUniverse)))))

(tu/deftest-kb every-leaf-kind-a-sentence-carries-is-decided
  ;; one root per kind, so no argument is waved through for want of a name.  A compound
  ;; is the exception and the only one: what `(f 5)` denotes is its function's business
  ;; (result), not its syntax's, so no kind would be the right answer.
  (let [p (tu/tmp-pred) f (tu/tmp-ind)]
    (doseq [e '[(genl string thing) (genl number thing) (genl integer number)
                (genl keyword thing) (genl boolean thing) (genl character thing)
                (genl symbol thing)]]
      (v/assert kb e 'CxUniverse))
    (v/assert kb (list 'unary_predicate p) 'CxUniverse)
    (v/assert kb (list 'arg p 1 'string) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (testing "a string is what the position asks for"
      (is (v/assert kb (list p "Bob") 'CxUniverse)))
    (testing "and every other kind is convicted rather than waved through"
      (doseq [x [5 5.5 :kw true \a]]
        (is (= :arg-type (ex-type #(v/assert kb (list p x) 'CxUniverse)))
            (str (pr-str x) " is not a string"))))
    (testing "a compound has no kind to be convicted by, and this one's function
             declares no result either"
      (is (v/assert kb (list p (list f 5)) 'CxUniverse)))))

(tu/deftest-kb the-openness-moved-to-the-declared-type
  ;; the check did not become closed-world, it moved where the doubt lives.  A `t` the
  ;; lattice cannot place a kind against is the imported-constraint case `quotedArg`
  ;; exempts for the same reason: convicting there would be judging by an absence.
  (let [p (tu/tmp-pred) floating (tu/tmp-type)]
    (v/assert kb '(genl string thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate p) 'CxUniverse)
    (v/assert kb (list 'arg p 1 floating) 'CxUniverse)   ; declared, but under no root
    (is (v/assert kb (list p "Bob") 'CxUniverse)
        "a type outside the hierarchy exempts the literal, as it does a symbol")))

;; ---- an application is typed by its function ------------------------------
;;
;; A **compound** argument holds no type membership and can hold none: a membership is
;; asserted of a name, and `(MsrFn 5 Meter)` is not one.  What the KB can know about it is
;; what its function is declared to yield — `(result F T)` for what an application *is*,
;; `(genlResult F T)` for what it is a kind *of* — so that is what the two checks read, and
;; they read it from the asking context's vantage like every other declaration.
;;
;; A **reifiable** function's application never reaches this arm.  It is minted into a
;; constant before the checks run and the constant carries the same declarations
;; materialized as `(T K)` / `(genl K T)`, which the symbol arm reads.  One declaration,
;; one verdict, whichever class the function is — which is what the last test here pins.
;;
;; Open-world throughout, one level out from the symbol reading: a function that declares
;; no result exempts every application of it, exactly as an unclassified symbol exempts
;; itself.

(tu/deftest-kb an-application-is-convicted-against-what-its-function-yields
  (let [msr (tu/tmp-type) dog (tu/tmp-type) f (tu/tmp-ind)
        wantsDog (tu/tmp-pred) wantsMsr (tu/tmp-pred)]
    (v/assert kb (list 'genl msr 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (v/assert kb (list 'unary_predicate wantsDog) 'CxUniverse)
    (v/assert kb (list 'arg wantsDog 1 dog) 'CxUniverse)
    (v/assert kb (list 'unary_predicate wantsMsr) 'CxUniverse)
    (v/assert kb (list 'arg wantsMsr 1 msr) 'CxUniverse)
    (testing "a function declaring no result exempts its applications"
      (is (v/assert kb (list wantsDog (list f 5 'Meter)) 'CxUniverse)))
    (v/assert kb (list 'result f msr) 'CxUniverse)
    (testing "the declaration is what makes the demand bite"
      (is (= :arg-type (ex-type #(v/assert kb (list wantsDog (list f 6 'Meter)) 'CxUniverse)))))
    (testing "and the same application satisfies a demand its result does reach"
      (is (v/assert kb (list wantsMsr (list f 7 'Meter)) 'CxUniverse)))
    (testing "the declaration arriving last reaches back over nothing, as the family does"
      (is (empty? (v/violations kb)))
      (is (v/ask? kb (list wantsDog (list f 5 'Meter)) 'CxUniverse)))))

(tu/deftest-kb a-head-declaring-several-results-is-admitted-where-any-of-them-reaches
  ;; a function yields one value and the declarations are claims about it, so the
  ;; application is all of them at once — one reaching the demand is the demand met
  (let [msr (tu/tmp-type) dog (tu/tmp-type) f (tu/tmp-ind) wants (tu/tmp-pred)]
    (v/assert kb (list 'genl msr 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (v/assert kb (list 'result f msr) 'CxUniverse)
    (v/assert kb (list 'result f dog) 'CxUniverse)
    (v/assert kb (list 'unary_predicate wants) 'CxUniverse)
    (v/assert kb (list 'arg wants 1 dog) 'CxUniverse)
    (is (v/assert kb (list wants (list f 1)) 'CxUniverse))))

(tu/deftest-kb a-declared-result-the-hierarchy-cannot-place-excuses-the-application
  ;; the openness moved to the declaration, exactly as it moved to a literal's declared
  ;; type: a result under no root is evidence the lattice cannot place, and convicting on
  ;; it would be judging by an absence
  (let [dog (tu/tmp-type) floating (tu/tmp-type) f (tu/tmp-ind) wants (tu/tmp-pred)]
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (v/assert kb (list 'result f floating) 'CxUniverse)   ; declared, but under no root
    (v/assert kb (list 'unary_predicate wants) 'CxUniverse)
    (v/assert kb (list 'arg wants 1 dog) 'CxUniverse)
    (is (v/assert kb (list wants (list f 1)) 'CxUniverse))))

(tu/deftest-kb an-instance-demand-reads-result-and-a-subtype-demand-reads-genlResult
  ;; the two are never crossed: `arg` asks what the application *is* and `result`
  ;; answers that; `genlArg` asks what it is a *kind of* and `genlResult` answers that.
  ;; A function declared under one of them is exempt from the other's demand.
  (let [root (tu/tmp-type) other (tu/tmp-type)
        isaFn (tu/tmp-ind) genlFn (tu/tmp-ind)
        inst (tu/tmp-pred) sub (tu/tmp-pred)]
    (v/assert kb (list 'genl root 'thing) 'CxUniverse)
    (v/assert kb (list 'genl other 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function isaFn) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function genlFn) 'CxUniverse)
    (v/assert kb (list 'result isaFn root) 'CxUniverse)
    (v/assert kb (list 'genlResult genlFn root) 'CxUniverse)
    (v/assert kb (list 'unary_predicate inst) 'CxUniverse)
    (v/assert kb (list 'arg inst 1 other) 'CxUniverse)
    (v/assert kb (list 'unary_predicate sub) 'CxUniverse)
    (v/assert kb (list 'genlArg sub 1 other) 'CxUniverse)
    (testing "the instance demand convicts on result"
      (is (= :arg-type (ex-type #(v/assert kb (list inst (list isaFn 1)) 'CxUniverse))))
      (is (v/assert kb (list inst (list genlFn 1)) 'CxUniverse)
          "and is exempt where the function declares only a genlResult"))
    (testing "the subtype demand convicts on genlResult"
      (is (= :arg-genl (ex-type #(v/assert kb (list sub (list genlFn 2)) 'CxUniverse))))
      (is (v/assert kb (list sub (list isaFn 2)) 'CxUniverse)
          "and is exempt where the function declares only a result"))))

(tu/deftest-kb a-subtype-demand-admits-the-application-its-declared-result-reaches
  (let [root (tu/tmp-type) sub' (tu/tmp-type) f (tu/tmp-ind) rel (tu/tmp-pred)]
    (v/assert kb (list 'genl root 'thing) 'CxUniverse)
    (v/assert kb (list 'genl sub' root) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (v/assert kb (list 'genlResult f sub') 'CxUniverse)
    (v/assert kb (list 'unary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'genlArg rel 1 root) 'CxUniverse)
    (is (v/assert kb (list rel (list f 1)) 'CxUniverse)
        "a declared result below the demanded kind is the demand met")))

(tu/deftest-kb a-quoting-predicates-payload-is-a-mention-and-is-not-typed-by-its-function
  ;; `(termOfUnit K E)` carries the NAT expression as a literal payload rather than as a
  ;; term used in that position, so what `E`'s function yields says nothing about the
  ;; argument — typing it would type a quotation by its referent.  The declaration here is
  ;; narrower than the shipped `(arg termOfUnit 2 thing)` on purpose, so the admission
  ;; rests on the exemption rather than on a type nothing can miss.
  (let [msr (tu/tmp-type) dog (tu/tmp-type) f (tu/tmp-ind) K (tu/tmp-ind)]
    (v/assert kb (list 'genl msr 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (v/assert kb (list 'result f msr) 'CxUniverse)
    (v/assert kb (list 'arg 'termOfUnit 2 dog) 'CxUniverse)
    (is (v/assert kb (list 'termOfUnit K (list f 5)) 'CxUniverse))))

(tu/deftest-kb a-result-declaration-a-context-cannot-see-does-not-refuse-it
  ;; the whole family judges from the asking context's vantage — a context is refused on
  ;; grounds it can see, and a declaration written in a sibling is not one of them
  (let [msr (tu/tmp-type) dog (tu/tmp-type) f (tu/tmp-ind) wants (tu/tmp-pred)
        seen (tu/tmp-ctx) sibling (tu/tmp-ctx)]
    (v/assert kb (list 'genl msr 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function f) 'CxUniverse)
    (v/assert kb (list 'unary_predicate wants) 'CxUniverse)
    (v/assert kb (list 'arg wants 1 dog) 'CxUniverse)
    (v/assert kb (list 'genlCx seen 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx sibling 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'result f msr) seen)
    (testing "the context the declaration is written in is refused by it"
      (is (= :arg-type (ex-type #(v/assert kb (list wants (list f 1)) seen)))))
    (testing "the sibling that cannot see it is not"
      (is (v/assert kb (list wants (list f 2)) sibling)))))

(tu/deftest-kb a-reifiable-application-is-convicted-through-the-constant-it-minted
  ;; the same declaration read at the other end: a `reifiable_function` application is
  ;; minted before the checks run, so `(msr K)` is materialized on the constant and the
  ;; ordinary symbol arm convicts it.  Both classes of function, one declaration, one
  ;; verdict — which is the whole of why the check reads `result` rather than inventing
  ;; a second declaration for the applications that are never minted.
  (let [msr (tu/tmp-type) dog (tu/tmp-type) f (tu/tmp-ind) wants (tu/tmp-pred)
        x (tu/tmp-ind)]
    (v/assert kb (list 'genl msr 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'reifiable_function f) 'CxUniverse)
    (v/assert kb (list 'result f msr) 'CxUniverse)
    (v/assert kb (list 'unary_predicate wants) 'CxUniverse)
    (v/assert kb (list 'arg wants 1 dog) 'CxUniverse)
    (is (= :arg-type (ex-type #(v/assert kb (list wants (list f x)) 'CxUniverse))))))
