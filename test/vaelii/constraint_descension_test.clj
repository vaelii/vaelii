;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-descension-test
  "A constraint declared of a predicate binds the tuples of every predicate beneath it.

  `(genl fatherOf parentOf)` says every `fatherOf` tuple **is** a `parentOf` tuple, and a
  tuple set only narrows going down — so `(arg parentOf 1 person)` is a claim about
  `fatherOf`'s first argument too.  Reading a declaration off the exact functor made the
  refusal *entry-point-dependent*: the ill-typed claim was refused under the general spelling,
  admitted under the specialized one, and then answered every general-spelling query
  through the matcher's own fan.  Every test here is a pair of entry points that must agree.

  The line this must not cross is the other direction: a **generative** property —
  `transitiveInArg`, `transitive`, `symmetric`, `reflexive` — is a claim about a relation
  and stays with the predicate that carries it.  Refusal-side constraints descend
  because tuples narrow; licences generate tuples and do not.  `inherit-test`'s
  `the-licence-stays-with-the-predicate-it-names` and `provers-test`'s
  `the-walk-reads-hops-through-the-subsumption-fan` pin that, and nothing here may move
  them."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defmacro with-entailing
  "Run the body with assertive argument types on — off by default, so the minting half
  of every entry-point-parity pair binds it."
  [& body]
  `(binding [checks/*assertive-arg-types?* true] ~@body))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw.  Named rather
  than `(thrown? ExceptionInfo …)`: a descension collapsing into a naming or arity
  refusal is exactly the regression a bare `thrown?` stays green through."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- orderings
  "Every arrival order of `xs`.  The multi-order cases below run over all of them rather
  than over a hand-picked few: which sentence of an incoherent set a refusal lands on is
  exactly what the order decides, so a subset would be choosing the answer."
  [xs]
  (if (< (count xs) 2)
    [(vec xs)]
    (for [x xs, tail (orderings (remove #{x} xs))]
      (into [x] tail))))

(defn- a-type [kb t ctx] (v/assert kb (list 'genl t 'thing) ctx))

(defn- believed?
  "Is `sentence` a **stored, believed** sentex in `ctx`?  Deliberately not `ask` — the
  minting half of an entry point pair is about a record existing, which a prover's answer is
  not."
  [kb sentence ctx]
  (let [h (v/handle-of kb sentence ctx)]
    (boolean (and h (v/in? kb h)))))

;; ---- entry point parity: the refusal ------------------------------------------

(tu/deftest-kb both-spellings-of-one-ill-typed-claim-are-refused
  ;; The headline.  Without the descension the second assert stores a fact that answers
  ;; the very query the first one was refused for.
  ;; Pinned to the constraint reading: what descends is asserted here as a *refusal* of both
  ;; spellings, and with the entailment on a symbol argument is minted rather than convicted
  ;; (docs/argtypes.md).  The declaration read through the edge is the subject either way —
  ;; the entailment descends through the same edges, and argtype_entail_test holds that half.
  (tu/without-entailing
   (tu/with-terms [person rock parentOf fatherOf TheRock1 Mary]
     (a-type kb person 'CxUniverse)
     (a-type kb rock 'CxUniverse)
     (v/assert kb (list rock TheRock1) 'CxUniverse)
     (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
     (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
     (is (= :arg-type (ex-type #(v/assert kb (list parentOf TheRock1 Mary) 'CxUniverse)))
         "the declaration's own predicate")
     (is (= :arg-type (ex-type #(v/assert kb (list fatherOf TheRock1 Mary) 'CxUniverse)))
         "and the sub-predicate, whose tuples are the same tuples")
     (testing "the refusal names the predicate the constraint was declared of"
       (is (re-find (re-pattern (str "declared of " parentOf))
                    (:message (first (v/check kb (list fatherOf TheRock1 Mary)
                                              'CxUniverse))))))
     (testing "and a well-typed claim under either spelling still stores"
       (tu/with-terms [Fred]
         (v/assert kb (list person Fred) 'CxUniverse)
         (is (v/assert kb (list parentOf Fred Mary) 'CxUniverse))
         (is (v/assert kb (list fatherOf Fred Mary) 'CxUniverse)))))))

(tu/deftest-kb genlArg-descends-on-the-same-argument
  (tu/with-terms [machine_t vehicle_t partType subPartType Rex]
    (a-type kb machine_t 'CxUniverse)
    (a-type kb vehicle_t 'CxUniverse)
    (v/assert kb (list 'genl subPartType partType) 'CxUniverse)
    (v/assert kb (list 'genlArg partType 1 machine_t) 'CxUniverse)
    (is (= :arg-genl (ex-type #(v/assert kb (list partType vehicle_t Rex) 'CxUniverse)))
        "a kind outside the constraint's down-closure")
    (is (= :arg-genl (ex-type #(v/assert kb (list subPartType vehicle_t Rex) 'CxUniverse)))
        "and the same kind under the sub-predicate")))

(tu/deftest-kb interArg-descends-by-riding-the-same-reader
  (tu/with-terms [carnivore meat plant eats gnawsOn Rex Chunk]
    (a-type kb carnivore 'CxUniverse)
    (a-type kb meat 'CxUniverse)
    (a-type kb plant 'CxUniverse)
    (v/assert kb (list 'genl gnawsOn eats) 'CxUniverse)
    (v/assert kb (list 'interArg eats 1 carnivore 2 meat) 'CxUniverse)
    (v/assert kb (list carnivore Rex) 'CxUniverse)
    (v/assert kb (list plant Chunk) 'CxUniverse)
    (is (= :inter-arg-type (ex-type #(v/assert kb (list eats Rex Chunk) 'CxUniverse))))
    (is (= :inter-arg-type (ex-type #(v/assert kb (list gnawsOn Rex Chunk) 'CxUniverse))))
    (testing "and the trigger still has to be established under either spelling"
      (tu/with-terms [Nobody]
        (is (v/assert kb (list gnawsOn Nobody Chunk) 'CxUniverse)
            "an untyped eater leaves the conditional dormant")))))

;; ---- entry point parity: the entailment ---------------------------------------

(tu/deftest-kb both-spellings-mint-and-the-edge-is-named-in-the-support
  (tu/with-terms [person parentOf fatherOf Fred Ann Mary]
    (with-entailing
      (a-type kb person 'CxUniverse)
      (let [eh (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
            dh (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
            ph (v/assert kb (list parentOf Fred Mary) 'CxUniverse)
            fh (v/assert kb (list fatherOf Ann Mary) 'CxUniverse)]
        (is (believed? kb (list person Fred) 'CxUniverse) "the declaration's own predicate")
        (is (believed? kb (list person Ann) 'CxUniverse) "and the sub-predicate")
        (testing "the direct mint rests on the fact and the declaration"
          (let [sup (first (:support (v/why kb (v/handle-of kb (list person Fred)
                                                            'CxUniverse))))]
            (is (= 'arg (:informant sup)))
            (is (= #{ph dh} (set (map :handle (:because sup)))))))
        (testing "the descended one rests on the genl edge as well — or retraction strands it"
          (let [sup (first (:support (v/why kb (v/handle-of kb (list person Ann)
                                                            'CxUniverse))))]
            (is (= #{fh dh eh} (set (map :handle (:because sup)))))))
        (testing "so dropping the edge takes the descended type back and leaves the direct one"
          (v/retract! kb eh)
          (is (not (believed? kb (list person Ann) 'CxUniverse)))
          (is (believed? kb (list person Fred) 'CxUniverse)))))))

(tu/deftest-kb the-inference-reading-descends-with-the-constraint-reading
  ;; `arg` reads two ways — a constraint when asserting, an inference when querying —
  ;; and the two must agree about *whose* declarations speak for a tuple.  A claim
  ;; refused for being ill-typed, under a declaration `ask` could not read, would be a
  ;; KB enforcing a constraint it cannot answer from.
  (tu/with-terms [person parentOf fatherOf Ann Mary]
    (a-type kb person 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
    (v/assert kb (list fatherOf Ann Mary) 'CxUniverse)
    (is (v/ask? kb (list person Ann) 'CxUniverse)
        "the super-predicate's declaration types the sub-predicate's argument")))

;; ---- scoping: the constraint applies where the edge is visible ----------

(tu/deftest-kb an-edge-a-writer-cannot-see-imports-no-constraint
  ;; The `genl` edge is as much a piece of evidence as the declaration and the
  ;; membership are, so it is held to the same vantage: a NAF check that convicted on
  ;; an edge asserted out of sight would convict harder the less a context sees.
  ;; Pinned for the reason above: the vantage rule is stated here as which context refuses.
  (tu/without-entailing
   (tu/with-terms [person rock parentOf fatherOf TheRock1 Mary CxLeft CxRight]
     (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
     (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
     (a-type kb person 'CxUniverse)
     (a-type kb rock 'CxUniverse)
     (v/assert kb (list rock TheRock1) 'CxUniverse)
     (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
     ;; the edge is asserted in a sibling context CxLeft cannot see
     (v/assert kb (list 'genl fatherOf parentOf) CxRight)
     (is (v/assert kb (list fatherOf TheRock1 Mary) CxLeft)
         "no visible edge, so no constraint descends")
     (is (= :arg-type (ex-type #(v/assert kb (list fatherOf TheRock1 Mary) CxRight)))
         "and where the edge is visible the constraint is"))))

;; ---- the three arrival orders ------------------------------------------

(tu/deftest-kb an-edge-arriving-after-the-facts-reports-and-refuses-nothing
  ;; The `arg` family has no retroactive reach — the conviction rests on the
  ;; *absence* of a path to the constraint type, so there is no second sentex to weigh
  ;; and a sweep would have to decide whether silence about a stored argument's type is
  ;; a violation or merely silence (docs/taxonomy.md, "What each constraint does in each
  ;; arrival order").  The descension inherits that verbatim rather than answering the
  ;; question through a side entry point: the edge arriving last is the family's third
  ;; ingredient, and it neither throws nor unstores.
  ;; Pinned for the reason above.  The absence this rests on is exactly what the entailment
  ;; reading fills in, so the two readings answer differently and this one names its own.
  (tu/without-entailing
   (tu/with-terms [person rock parentOf fatherOf TheRock1 Mary]
     (a-type kb person 'CxUniverse)
     (a-type kb rock 'CxUniverse)
     (v/assert kb (list rock TheRock1) 'CxUniverse)
     (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
     (let [fh (v/assert kb (list fatherOf TheRock1 Mary) 'CxUniverse)]
       (v/clear-violations! kb)
       (is (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
           "the edge is admitted, not refused for what it retroactively convicts")
       (is (v/in? kb fh) "and the fact it now convicts stays stored and believed")
       (is (empty? (filter #(= :arg-type (:violation %)) (v/violations kb))))
       (testing "what does change is that the next such claim is refused"
         (tu/with-terms [TheRock2]
           (v/assert kb (list rock TheRock2) 'CxUniverse)
           (is (= :arg-type (ex-type #(v/assert kb (list fatherOf TheRock2 Mary)
                                                'CxUniverse))))))))))

(tu/deftest-kb every-arrival-order-of-the-three-ingredients-mints-the-same-type
  ;; Storage may differ by arrival order — that is the documented contract for a
  ;; constraint arriving after a fact — but what a KB holding all three ingredients
  ;; *entails* may not.  Fact, declaration and edge, in all six orders.
  (doseq [order [[:fact :decl :edge] [:fact :edge :decl] [:decl :fact :edge]
                 [:decl :edge :fact] [:edge :fact :decl] [:edge :decl :fact]]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [person parentOf fatherOf Ann Mary]
        (with-entailing
          (a-type kb person 'CxUniverse)
          (let [step {:fact #(v/assert kb (list fatherOf Ann Mary) 'CxUniverse)
                      :decl #(v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
                      :edge #(v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)}]
            (doseq [s order] ((step s))))
          (is (believed? kb (list person Ann) 'CxUniverse)
              (str "entailed under " (pr-str order))))))))

;; ---- what does not move ------------------------------------------------
;;
;; The family divides by **direction**, and the division is the whole of why descending
;; the constraints is sound.  `arity`, `asymmetric`, `functional` and the argument
;; declarations *refuse* tuples, and a sub-predicate's tuples are the super's, so a
;; refusal above is a refusal below.  `transitive`, `symmetric`, `reflexive` and
;; `transitiveInArg` *license* tuples, and a licence read for a predicate nobody declared
;; it of manufactures knowledge — dogs may be larger than cats without every subkind
;; being much larger.  So the generative four stay exactly where they were stated.
;;
;; `transitiveInArg` is pinned by `inherit-test`'s `the-licence-stays-with-the-predicate-
;; it-names` and `transitive` by `provers-test`'s `the-walk-reads-hops-through-the-
;; subsumption-fan`.  The other two are here, because a property that quietly began to
;; descend would not fail any test that only checks the refusing four.

(tu/deftest-kb symmetric-does-not-descend-to-a-sub-predicate
  ;; `(symmetric relatedTo)` says *relatedTo* reads both ways.  It says nothing about a
  ;; specialization: siblings are related, and being someone's sibling both ways is a
  ;; different claim from being related both ways.
  (tu/with-terms [relatedTo siblingOf A B]
    (v/with-deferred-settle kb
      (v/assert kb (list 'symmetric relatedTo) 'CxUniverse)
      (v/assert kb (list 'genl siblingOf relatedTo) 'CxUniverse))
    (v/assert kb (list siblingOf A B) 'CxUniverse)
    (is (v/ask? kb (list relatedTo B A) 'CxUniverse)
        "the super-predicate's own licence reads the sub-predicate's fact backwards")
    (is (not (v/ask? kb (list siblingOf B A) 'CxUniverse))
        "but the sub-predicate is not symmetric until somebody says so")))

(tu/deftest-kb reflexive-does-not-descend-to-a-sub-predicate
  ;; the same claim for the other generative mark: a licence to conclude `(P a a)` for
  ;; everything `P` relates is a claim about `P`.
  (tu/with-terms [sameSizeAs sameWidthAs A B]
    (v/with-deferred-settle kb
      (v/assert kb (list 'reflexive sameSizeAs) 'CxUniverse)
      (v/assert kb (list 'genl sameWidthAs sameSizeAs) 'CxUniverse))
    (v/assert kb (list sameWidthAs A B) 'CxUniverse)
    (is (v/ask? kb (list sameSizeAs A A) 'CxUniverse)
        "the super-predicate's own licence holds of what it relates")
    (is (not (v/ask? kb (list sameWidthAs A A) 'CxUniverse))
        "the sub-predicate's does not, nobody having declared it reflexive")))

;; ---- arity -------------------------------------------------------------
;;
;; The cheapest member of the family: a `fatherOf` tuple *is* a `parentOf` tuple, so its
;; length is held to what `parentOf` was declared with.  It is also the strictest, and the
;; only one that refuses a **declaration** rather than only a tuple: the other constraints
;; narrow going down, so a sub-predicate may add to them, while a length cannot be
;; narrowed — a `genl` edge across two different lengths is a claim that two tuple sets of
;; different shapes are one set, which is not a stricter claim but an unmeanable one.  So
;; the hierarchy is read where the predicate declares nothing, and where it declares
;; something the two are held to agree.

(tu/deftest-kb an-undeclared-sub-predicate-takes-its-supers-arity
  (tu/with-terms [parentOf fatherOf A B C]
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (is (v/assert kb (list fatherOf A B) 'CxUniverse) "the inherited length stores")
    (is (= :arity (ex-type #(v/assert kb (list fatherOf A B C) 'CxUniverse)))
        "and a ternary fatherOf fact is a ternary parentOf tuple, which is refused")
    (testing "the refusal names the predicate the length was read off, as inherited"
      ;; and words it as inherited: `fatherOf` declared nothing, so "is declared with"
      ;; would send an author looking for a declaration that does not exist.  The
      ;; retroactive report reads the same `:via` and makes the same split.
      (let [m (:message (first (v/check kb (list fatherOf A B C) 'CxUniverse)))]
        (is (re-find (re-pattern (str "takes 2 arguments through " parentOf)) m))
        (is (not (re-find #"is declared with" m))
            "the wording credits no declaration fatherOf never had")))
    (testing "and it convicts against that predicate's own declaration"
      (is (= (v/handle-of kb (list 'binary_predicate parentOf) 'CxUniverse)
             (:opposing-handle (first (v/check kb (list fatherOf A B C) 'CxUniverse))))))))

(tu/deftest-kb the-entry-point-and-the-report-word-one-binding-the-same-way
  ;; The two halves describe the same fact about the same KB, so a length read off a
  ;; super must read as inherited at both, and one declared of the predicate itself must
  ;; read as declared at both.  They were split: the report said "takes 2 arguments
  ;; through parentOf" while the entry point said "is declared with 2 arguments, declared of
  ;; parentOf" — one binding, two descriptions, and the entry point's credited a declaration
  ;; `fatherOf` never carried.
  (letfn [(entry-point [kb sen] (:message (first (v/check kb sen 'CxUniverse))))]
    (testing "inherited: both say takes … through"
      (tu/with-terms [parentOf fatherOf A B C]
        (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
        (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
        (is (re-find (re-pattern (str "takes 2 arguments through " parentOf))
                     (entry-point kb (list fatherOf A B C))))))
    (testing "declared of itself: both say is declared with, and name no via"
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [parentOf A B C]
          (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
          (let [m (entry-point kb (list parentOf A B C))]
            (is (re-find #"is declared with 2 arguments" m))
            (is (not (re-find #"through" m))
                "nothing to credit, so no clause crediting it")))))))

(tu/deftest-kb a-signature-on-the-sub-predicate-must-match-the-supers
  ;; **The boundary `vaelii/vaelii#23` drew has moved, and #23's own argument is what
  ;; moves it.**  #23 preserves `arg`, `genlArg` and `interArg` down the hierarchy
  ;; and excludes `arity` for one stated reason: the engine permitted a specialization to
  ;; carry a different signature from its parent, so preserving the parent's arity
  ;; downward could have made `(functional arity)` answer both the inherited and the
  ;; explicit value for the child.  That reason is a consequence of permitting the
  ;; mismatched pair, not an argument for permitting it.  Refuse the pair — as this does —
  ;; and no specialization *has* a different signature, so the hazard #23 avoided cannot
  ;; arise and the property it was protecting holds for a stronger reason than the
  ;; carve-out gave it (`the-arity-table-still-answers-one-value-per-predicate`, below).
  ;;
  ;; What the edge asserts is why: `(genl fatherOf parentOf)` says every `fatherOf` tuple
  ;; **is** a `parentOf` tuple, and tuples of different lengths are not the same tuples.
  ;; A pair the KB cannot mean is refused whichever of its three sentences arrives last.
  (let [ingredients [:edge :super-declaration :sub-declaration]]
    (doseq [last-in ingredients]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [parentOf fatherOf]
          (let [sentence {:edge              (list 'genl fatherOf parentOf)
                          :super-declaration (list 'arity parentOf 2)
                          :sub-declaration   (list 'arity fatherOf 3)}
                arriving (sentence last-in)]
            (doseq [s ingredients :when (not= s last-in)]
              (v/assert kb (sentence s) 'CxUniverse))
            (is (= :arity (ex-type #(v/assert kb arriving 'CxUniverse)))
                (str "refused with " (name last-in) " arriving last"))
            (testing "and the refusal names both predicates and both arities"
              (let [m (:message (first (v/check kb arriving 'CxUniverse)))]
                (is (re-find (re-pattern (str "3 arguments declared of " fatherOf)) m)
                    (str "the sub's arity, with " (name last-in) " last"))
                (is (re-find (re-pattern (str "2 declared of " parentOf)) m)
                    (str "the super's arity, with " (name last-in) " last"))))))))))

(tu/deftest-kb the-predicate-type-spelling-of-a-signature-must-match-too
  ;; Both spellings declare an arity and `inherited-arity` reads both, so the refusal
  ;; reads both: a KB loaded without CxCore's derivation rules has only what somebody
  ;; typed, and a rule that saw the `(arity P n)` table and not the membership would
  ;; refuse or admit by which spelling its author happened to pick.
  (doseq [last-in [:edge :sub-declaration]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [parentOf fatherOf]
        (let [sentence {:edge            (list 'genl fatherOf parentOf)
                        :sub-declaration (list 'ternary_predicate fatherOf)}]
          (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
          (doseq [s [:edge :sub-declaration] :when (not= s last-in)]
            (v/assert kb (sentence s) 'CxUniverse))
          (is (= :arity (ex-type #(v/assert kb (sentence last-in) 'CxUniverse)))
              (str "refused with " (name last-in) " arriving last")))))))

(tu/deftest-kb the-arity-table-still-answers-one-value-per-predicate
  ;; The property `vaelii/vaelii#23` was protecting, and the reason its carve-out is no
  ;; longer what protects it.  The table is still untouched by the descension — a
  ;; predicate that declares nothing answers nothing, and takes its length as a *check*
  ;; rather than as an answerable fact — and now a conflicting write cannot land either,
  ;; so `(functional arity)` has one value to be functional about on both counts.
  (tu/with-terms [parentOf fatherOf A B]
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (is (v/assert kb (list fatherOf A B) 'CxUniverse)
        "the inherited length binds the tuple")
    (is (empty? (v/ask kb (list 'arity fatherOf '?n) 'CxUniverse))
        "and is not preserved as a fact — nobody wrote an arity of fatherOf")
    (testing "a matching declaration of its own is one value, not a second one"
      (v/assert kb (list 'arity fatherOf 2) 'CxUniverse)
      (is (= 1 (count (v/ask kb (list 'arity fatherOf '?n) 'CxUniverse)))))
    (testing "and the write that would have made two is what is refused"
      (is (= :arity (ex-type #(v/assert kb (list 'arity fatherOf 3) 'CxUniverse))))
      (is (= 1 (count (v/ask kb (list 'arity fatherOf '?n) 'CxUniverse)))))))

(tu/deftest-kb every-arrival-order-of-an-arity-clash-leaves-the-pair-agreeing
  ;; Storage may differ by arrival order — the sentence refused is whichever arrived onto
  ;; a KB the rest of the pair was already in, which is the first-writer-wins every entry point
  ;; refusal has.  What may *not* differ is the state that leaves: in all 24 orders of the
  ;; edge, the two declarations and a tuple, the KB never ends up holding two genl-related
  ;; predicates declared at different lengths, and never answers two arities for one
  ;; predicate.
  (doseq [order (orderings [:edge :super-declaration :sub-declaration :tuple])]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [parentOf fatherOf A B C]
        (let [step {:edge              #(v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
                    :super-declaration #(v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
                    :sub-declaration   #(v/assert kb (list 'ternary_predicate fatherOf) 'CxUniverse)
                    :tuple             #(v/assert kb (list fatherOf A B C) 'CxUniverse)}]
          (doseq [s order] (ex-type (step s)))
          ;; Read through the entry point, not off the `arity` table.  A `binary_predicate`
          ;; membership is the *other* spelling of a declaration and populates no table
          ;; without CxCore's derivation rules, so `(ask (arity P ?n))` answers `()` here
          ;; in every order — a comparison of two empty seqs, true by arithmetic, under
          ;; every arrangement including the broken ones.  What a length declaration means
          ;; is which tuples the predicate admits, so that is what is compared.
          (let [admits (fn [p] (into #{} (filter #(empty? (v/check kb (apply list p (take % [A B C]))
                                                                   'CxUniverse)))
                                     [1 2 3]))
                sub    (admits fatherOf)
                super  (admits parentOf)
                edge?  (v/ask? kb (list 'genl fatherOf parentOf) 'CxUniverse)]
            (is (seq (into sub super))
                (str "the probe reads something at all, under " (pr-str order)))
            (when edge?
              ;; containment, not equality: the edge says every fatherOf tuple is a
              ;; parentOf tuple, so the sub's lengths have to be lengths the super
              ;; admits — an *undeclared* super admits all three and is broader than
              ;; its sub legitimately.  What the pair may not hold is a sub admitting
              ;; a length its super refuses, which is the incoherent state itself.
              (is (every? super sub)
                  (str "the edge stands, so every length fatherOf admits parentOf "
                       "admits — fatherOf " (pr-str sub) ", parentOf " (pr-str super)
                       ", under " (pr-str order))))))))))

(tu/deftest-kb an-undeclared-predicate-between-two-declared-ones-is-still-a-pair
  ;; The pair `edge-arity-problem` reads through the closures for.  A predicate that
  ;; declares nothing is not a predicate that binds nothing — it takes a length from above
  ;; and hands one down — so an edge onto it carries the clash even though neither of its
  ;; own endpoints is the one declared.  Reading the two endpoints' own declarations leaves
  ;; both edges looking innocent and the KB answering `(parentOf ?a ?b ?c)` with a tuple
  ;; `(assert (parentOf X Y Z))` refuses.
  ;;
  ;; Both edge orders, because each stops on a different undeclared side: with the lower
  ;; edge already in, the length is above the arriving edge's super (`inherited-arity`);
  ;; with the upper edge already in, it is below its sub (`descended-arity`).
  (doseq [[label edges] [[:lower-first  [[:f>p] [:g>f]]]
                         [:upper-first  [[:g>f] [:f>p]]]]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [parentOf fatherOf grandOf A B C]
        (let [edge {:f>p #(v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
                    :g>f #(v/assert kb (list 'genl grandOf fatherOf) 'CxUniverse)}]
          (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
          (v/assert kb (list 'ternary_predicate grandOf) 'CxUniverse)
          (let [types (mapv #(ex-type (edge (first %))) edges)]
            (is (some #{:arity} types)
                (str "one of the two edges is refused, " (name label)
                     " — got " (pr-str types))))
          (testing "and the chain the refusal broke answers nothing the entry point would refuse"
            (when (v/ask? kb (list 'genl grandOf parentOf) 'CxUniverse)
              (ex-type #(v/assert kb (list grandOf A B C) 'CxUniverse))
              (is (= (empty? (v/check kb (list parentOf A B C) 'CxUniverse))
                     (pos? (count (v/ask kb (list parentOf '?a '?b '?c) 'CxUniverse))))
                  (str "answers a ternary parentOf exactly where it admits one, "
                       (name label))))))))))

(tu/deftest-kb a-membership-spelled-through-a-subtype-declares-the-same-arity
  ;; `checks/membership-arity`'s reason.  `membered-arity` answers off the *closure* of a
  ;; term's types, so `(genl myBinPred binary_predicate)` beside `(myBinPred fatherOf)`
  ;; makes `fatherOf` binary to every reader of a declaration.  A writer of one that
  ;; matched the three literal functors admitted the disagreeing edge in one arrival order
  ;; and refused it in the other, leaving a KB whose facts the reader then convicts.
  (doseq [[label order] [[:membership-first [:membership :edge]]
                         [:edge-first       [:edge :membership]]]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [myBinPred parentOf fatherOf A B C]
        (let [step {:membership #(v/assert kb (list myBinPred fatherOf) 'CxUniverse)
                    :edge       #(v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)}]
          (v/assert kb (list 'genl myBinPred 'binary_predicate) 'CxUniverse)
          (v/assert kb (list 'ternary_predicate parentOf) 'CxUniverse)
          (is (some #{:arity} (mapv #(ex-type (step %)) order))
              (str "the pair is refused whichever of the two arrives last, " (name label)))
          (testing "and what fatherOf admits is what it answers"
            (doseq [n [2 3]]
              (let [tuple (apply list fatherOf (take n [A B C]))]
                (ex-type #(v/assert kb tuple 'CxUniverse))
                (is (= (empty? (v/check kb tuple 'CxUniverse))
                       (v/ask? kb tuple 'CxUniverse))
                    (str n "-tuple, " (name label)))))))))))

(tu/deftest-kb supers-that-disagree-about-arity-bind-nothing
  ;; The stance `tax/declared-arity` already takes toward two contradictory declarations
  ;; of one predicate, read one level up: unsettled is not the same as undeclared, and it
  ;; constrains the same.
  (tu/with-terms [leftOf rightOf bothOf A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl bothOf leftOf) 'CxUniverse)
      (v/assert kb (list 'genl bothOf rightOf) 'CxUniverse)
      (v/assert kb (list 'arity leftOf 2) 'CxUniverse)
      (v/assert kb (list 'arity rightOf 3) 'CxUniverse))
    (is (v/assert kb (list bothOf A B) 'CxUniverse))
    (is (v/assert kb (list bothOf A B C) 'CxUniverse)
        "no unanimous answer above it, so nothing binds")))

(tu/deftest-kb a-variableArity-super-releases-the-inheritance
  (tu/with-terms [chainOf subChainOf A B C]
    (v/assert kb (list 'binary_predicate chainOf) 'CxUniverse)
    (v/assert kb (list 'genl subChainOf chainOf) 'CxUniverse)
    (is (= :arity (ex-type #(v/assert kb (list subChainOf A B C) 'CxUniverse))))
    (v/assert kb (list 'variable_arity chainOf) 'CxUniverse)
    (testing "a relation that reads a chain of any length binds nothing beneath it to one"
      (is (v/assert kb (list subChainOf A B C) 'CxUniverse)))))

(tu/deftest-kb a-variableArity-super-releases-it-without-declaring-a-length-itself
  ;; the case above gives the releasing super an arity of its own, so it is one of the
  ;; supers that contributed the number being released.  A super marked `variable_arity`
  ;; and given no length says the same thing about the hierarchy under it, and has to
  ;; release the same way — otherwise it sits above the predicate saying nothing, while a
  ;; sibling's binary declaration refuses the chain it exists to license.
  (tu/with-terms [chainOf otherOf subOf A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'variable_arity chainOf) 'CxUniverse)
      (v/assert kb (list 'binary_predicate otherOf) 'CxUniverse)
      (v/assert kb (list 'genl subOf chainOf) 'CxUniverse)
      (v/assert kb (list 'genl subOf otherOf) 'CxUniverse))
    (is (v/assert kb (list subOf A B C) 'CxUniverse)
        "the variable_arity super releases what the binary one would have bound")))

(tu/deftest-kb variable_arity-on-either-side-releases-the-match-across-the-edge
  ;; The declared exception to the rule above, and it is one mark rather than two: a
  ;; relation that reads a chain of any length makes no claim about the length of the
  ;; tuples above or below it, so there is nothing for a second declaration to contradict
  ;; — whichever end of the edge carries the mark, and whichever sentence arrives last.
  (doseq [marked  [:sub :super]
          last-in [:edge :sub-declaration]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [chainOf subChainOf A B C]
        (let [sentence {:edge            (list 'genl subChainOf chainOf)
                        :sub-declaration (list 'ternary_predicate subChainOf)}]
          (v/assert kb (list 'binary_predicate chainOf) 'CxUniverse)
          (v/assert kb (list 'variable_arity (if (= marked :sub) subChainOf chainOf))
                    'CxUniverse)
          (doseq [s [:edge :sub-declaration] :when (not= s last-in)]
            (v/assert kb (sentence s) 'CxUniverse))
          (is (v/assert kb (sentence last-in) 'CxUniverse)
              (str "released with the mark on the " (name marked)
                   " and " (name last-in) " last"))
          (is (v/assert kb (list subChainOf A B C) 'CxUniverse)
              "and the chain it exists to license still stores"))))))

;; ---- asymmetric --------------------------------------------------------
;;
;; The converse probe already fanned *down* the hierarchy; only the mark was read off the
;; exact functor.  So which spelling arrived second decided whether the pair was found.

(tu/deftest-kb an-asymmetric-super-convicts-a-sub-predicate-in-both-orders
  (doseq [order [:general-first :specialized-first]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [largerThan muchLargerThan A B]
        (v/assert kb (list 'asymmetric largerThan) 'CxUniverse)
        (v/assert kb (list 'genl muchLargerThan largerThan) 'CxUniverse)
        (let [general #(v/assert kb (list largerThan A B) 'CxUniverse {:strength :monotonic})
              special #(v/assert kb (list muchLargerThan B A) 'CxUniverse {:strength :monotonic})]
          (if (= order :general-first) (general) (special))
          (is (= :asymmetric (ex-type (if (= order :general-first) special general)))
              (str "the converse is refused under " (name order))))))))

(tu/deftest-kb the-asymmetry-refusal-names-the-predicate-the-mark-is-on
  (tu/with-terms [largerThan muchLargerThan A B]
    (v/assert kb (list 'asymmetric largerThan) 'CxUniverse)
    (v/assert kb (list 'genl muchLargerThan largerThan) 'CxUniverse)
    (v/assert kb (list muchLargerThan A B) 'CxUniverse {:strength :monotonic})
    (is (re-find (re-pattern (str "asymmetric: " largerThan " cannot hold both ways"))
                 (:message (first (v/check kb (list muchLargerThan B A) 'CxUniverse)))))))

;; ---- functional --------------------------------------------------------

(tu/deftest-kb a-functional-super-reconciles-a-sub-predicates-fillers
  ;; The mint has to name the `genl` edge as well as the declaration: the merge rests on
  ;; the subsumption that made the two fillers one slot's, so retracting the edge has to
  ;; take it back rather than leave two names merged on a declaration that no longer
  ;; reaches them.
  (tu/with-terms [motherOf birthMotherOf Tom]
    ;; the derived equality is stored with its arguments in content order, so the
    ;; two spellings are sorted here rather than guessed at
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
          dh (v/assert kb (list 'functional motherOf) 'CxUniverse)
          eh (v/assert kb (list 'genl birthMotherOf motherOf) 'CxUniverse)
          f1 (v/assert kb (list birthMotherOf Tom lo) 'CxUniverse)]
      (v/assert kb (list birthMotherOf Tom hi) 'CxUniverse)
      (is (v/same-class? kb lo hi) "two fillers of one motherOf-level slot are one thing")
      (testing "and the merge names the fact, the declaration and the edge"
        (let [eq  (v/handle-of kb (list 'equals lo hi) 'CxUniverse)
              sup (first (:support (v/why kb eq)))]
          (is (some? eq) "no derived equality to explain")
          (is (= 'functional (:informant sup)))
          (is (contains? (set (map :handle (:because sup))) eh) "the genl edge")
          (is (contains? (set (map :handle (:because sup))) dh) "the declaration")
          (is (contains? (set (map :handle (:because sup))) f1) "the standing fact")))
      (testing "so dropping the edge un-merges them"
        (v/retract! kb eh)
        (is (not (v/same-class? kb lo hi)))))))

(tu/deftest-kb a-descended-merge-rests-on-both-spellings-edges
  ;; The case above spells both fillers the same way, so one edge carries the whole
  ;; descent.  Spell them differently and the pair has two sides that reached the marked
  ;; predicate independently: naming only the arriving sentence's descent left the merge
  ;; standing after the *other* fact stopped being a `parentOf` tuple at all, which is the
  ;; failure `edge-support` exists to prevent, avoided on one side only.
  (tu/with-terms [parentOf fatherOf motherOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional parentOf) 'CxUniverse)
      (let [ef (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
            em (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse)]
        (v/assert kb (list motherOf Tom lo) 'CxUniverse)
        (v/assert kb (list fatherOf Tom hi) 'CxUniverse)
        (is (v/same-class? kb lo hi) "one parentOf slot, two fillers, merged")
        (testing "and the merge names both descents"
          (let [eq (v/handle-of kb (list 'equals lo hi) 'CxUniverse)
                because (set (map :handle (:because (first (:support (v/why kb eq))))))]
            (is (some? eq) "no derived equality to explain")
            (is (contains? because ef) "the arriving sentence's edge")
            (is (contains? because em) "and the stored filler's, equally an ingredient")))
        (testing "so retracting the stored filler's edge un-merges too"
          (v/retract! kb em)
          (is (not (v/same-class? kb lo hi))
              "the motherOf fact is not a parentOf tuple now, so nothing licenses it"))))))

(tu/deftest-kb a-descended-merge-names-each-edge-once
  ;; The two descents are a *set*.  Where the sides share a hop — and the commonest pair
  ;; of all, two fillers of one functor, shares every hop — appending them listed the
  ;; same edge two or three times in the record `derive-equality` stores.  Belief never
  ;; moved, which is what made it read as cosmetic: an antecedent list is the explanation
  ;; a caller is handed, and one counting a single edge twice describes a justification
  ;; the KB does not hold.
  (letfn [(antecedents [kb lo hi]
            (let [eq (v/handle-of kb (list 'equals lo hi) 'CxUniverse)]
              (mapv :handle (:because (first (:support (v/why kb eq)))))))]
    (testing "one functor on both sides, so both descents are the same single edge"
      (tu/with-terms [parentOf fatherOf Tom]
        (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
          (v/assert kb (list 'functional parentOf) 'CxUniverse)
          (let [ef (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)]
            (v/assert kb (list fatherOf Tom lo) 'CxUniverse)
            (v/assert kb (list fatherOf Tom hi) 'CxUniverse)
            (is (v/same-class? kb lo hi) "one parentOf slot, two fillers, merged")
            (let [as (antecedents kb lo hi)]
              (is (= 1 (count (filter #{ef} as)))
                  "the one edge both sides descended is named once")
              (is (= (count as) (count (distinct as)))
                  "and no antecedent is listed twice"))))))
    (testing "and a shared hop is named once where the sides descend different distances"
      ;; dadOf → fatherOf → parentOf beside fatherOf → parentOf: the second hop is on
      ;; both paths, so a concatenation duplicates it even though the functors differ.
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [parentOf fatherOf dadOf Tom]
          (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
            (v/assert kb (list 'functional parentOf) 'CxUniverse)
            (let [ef (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
                  ed (v/assert kb (list 'genl dadOf fatherOf) 'CxUniverse)]
              (v/assert kb (list fatherOf Tom lo) 'CxUniverse)
              (v/assert kb (list dadOf Tom hi) 'CxUniverse)
              (is (v/same-class? kb lo hi) "both are parentOf tuples, so the pair merges")
              (let [as (antecedents kb lo hi)]
                (is (= 1 (count (filter #{ef} as))) "the shared hop, named once")
                (is (= 1 (count (filter #{ed} as))) "and the hop only one side takes")
                (is (= (count as) (count (distinct as)))))
              (testing "and each edge still carries the merge, deduped or not"
                (v/retract! kb ef)
                (is (not (v/same-class? kb lo hi))
                    "the shared hop is gone, so neither fact is a parentOf tuple")))))))))

(tu/deftest-kb a-mark-that-never-covered-the-pair-does-not-hold-the-merge
  ;; `functional-clashes` reports which mark convicted, and the merge rests on that one.
  ;; Justifying it with every marked predicate above the arriving functor instead let a
  ;; mark above only *one* of the two spellings hold the merge up after the only
  ;; declaration that ever reached both was retracted.
  (tu/with-terms [parentOf guardianOf fatherOf motherOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
          dp (v/assert kb (list 'functional parentOf) 'CxUniverse)]
      (v/with-deferred-settle kb
        (v/assert kb (list 'functional guardianOf) 'CxUniverse)
        (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
        (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse)
        ;; guardianOf is above fatherOf and nothing else
        (v/assert kb (list 'genl fatherOf guardianOf) 'CxUniverse))
      (v/assert kb (list motherOf Tom lo) 'CxUniverse)
      (v/assert kb (list fatherOf Tom hi) 'CxUniverse)
      (is (v/same-class? kb lo hi) "parentOf is above both spellings, so the pair merges")
      (testing "and guardianOf, above one of them, never licensed it"
        (v/retract! kb dp)
        (is (not (v/same-class? kb lo hi))
            "retracting the only mark that reached both takes the merge with it")))))

(tu/deftest-kb every-arrival-order-of-a-descended-functional-merge-agrees
  (doseq [order [[:f1 :f2 :decl :edge] [:edge :decl :f1 :f2] [:decl :f1 :f2 :edge]
                 [:f1 :edge :f2 :decl] [:f1 :decl :f2 :edge]]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [motherOf birthMotherOf Tom]
        (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
              step {:f1   #(v/assert kb (list birthMotherOf Tom lo) 'CxUniverse)
                    :f2   #(v/assert kb (list birthMotherOf Tom hi) 'CxUniverse)
                    :decl #(v/assert kb (list 'functional motherOf) 'CxUniverse)
                    :edge #(v/assert kb (list 'genl birthMotherOf motherOf) 'CxUniverse)}]
          (doseq [s order] ((step s)))
          (is (v/same-class? kb lo hi) (str "merged under " (pr-str order))))))))

(tu/deftest-kb a-numeric-clash-under-a-descended-mark-is-still-the-hard-refusal
  ;; No merge can make two numbers one thing, so the descension carries the rejection
  ;; down rather than the equality.
  (tu/with-terms [birthYearOf bornInYear Tom]
    (v/assert kb (list 'functional birthYearOf) 'CxUniverse)
    (v/assert kb (list 'genl bornInYear birthYearOf) 'CxUniverse)
    (v/assert kb (list bornInYear Tom 1980) 'CxUniverse)
    (is (= :functional (ex-type #(v/assert kb (list bornInYear Tom 1990) 'CxUniverse))))
    (is (re-find (re-pattern (str "functional violation: " birthYearOf))
                 (:message (first (v/check kb (list bornInYear Tom 1990) 'CxUniverse)))))))

;; ---- what does not move ------------------------------------------------

(tu/deftest-kb a-declarations-own-checks-read-its-own-predicates-arity
  ;; `declaration-problem` runs on the declaration rather than on the content it
  ;; constrains, and it asks whether the *declaring* predicate has the position named.
  ;; The descension is about which tuples a declaration reaches, not about which
  ;; positions the predicate it names has.
  ;;
  ;; Two genl-related predicates of different lengths is the one shape the arity rule
  ;; refuses, so the pair that makes the point is the one it exempts: `variable_arity` on
  ;; the sub releases the match, and the two lengths stand side by side to be read off
  ;; separately.
  (tu/with-terms [parentOf fatherOf]
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list 'variable_arity fatherOf) 'CxUniverse)
    (v/assert kb (list 'ternary_predicate fatherOf) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (is (= :arg-position (ex-type #(v/assert kb (list 'arg parentOf 3 'thing)
                                             'CxUniverse)))
        "parentOf is binary, whatever its sub-predicates are")
    (is (v/assert kb (list 'arg fatherOf 3 'thing) 'CxUniverse)
        "and fatherOf is ternary, whatever its super-predicates are")))

;; ---- the retroactive report descends too --------------------------------
;;
;; The entry point reads `declared-arity`, so it refuses a wrong-arity sentence whether the
;; length was declared of the predicate or inherited from a super.  The **retroactive**
;; half — `settle/report-arity-reach!`, the finding filed for facts stored before
;; anything existed to refuse them — read only its own trigger's predicate, so it went
;; silent in exactly the two arrival orders the descension created: the edge arriving
;; last, and the declaration landing on the super.  A fact silently stored and a fact
;; reported is the difference the whole retroactive half exists to remove.

(defn- arity-findings
  "The retroactive arity reports in the ledger, by the predicate each is about."
  [kb]
  (into {} (for [e (v/violations kb) :when (= :arity (:violation e))]
             [(:predicate (:detail e)) (:detail e)])))

(tu/deftest-kb an-edge-arriving-last-reports-the-facts-it-newly-convicts
  ;; The third ingredient.  `fatherOf` is bound to no length while the tuple is written,
  ;; so the entry point cannot refuse it; the edge is what makes it wrong, and before this the
  ;; edge filed nothing — leaving the fact stored, believed and unmentioned while the
  ;; very next assert of the same shape was refused.
  (tu/with-terms [parentOf fatherOf A B C]
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list fatherOf A B C) 'CxUniverse)
    (is (empty? (arity-findings kb)) "nothing binds fatherOf yet, so nothing is wrong")
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (let [e (get (arity-findings kb) fatherOf)]
      (is (some? e) "the edge files the finding")
      (is (= 2 (:expected e)))
      (is (= parentOf (:via e)) "the length was read off the super")
      (is (= [(list fatherOf A B C)] (:sample e)))
      (is (v/ask? kb (list fatherOf A B C) 'CxUniverse)
          "reported, not withdrawn — the edge moves no belief either"))))

(tu/deftest-kb a-declaration-landing-on-the-super-reaches-the-sub-predicates-facts
  ;; The trigger fires here even without the edge arm — `arity-bound-by` answers
  ;; `parentOf` — and the sweep still found nothing, because it read the extent off the
  ;; named predicate alone.  `parentOf` has no facts; `fatherOf` has the wrong one.
  (tu/with-terms [parentOf fatherOf A B C]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list fatherOf A B C) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (let [fs (arity-findings kb)]
      (is (= [fatherOf] (keys fs))
          "the finding is about the predicate whose facts are wrong, not the one declared")
      (is (= parentOf (:via (get fs fatherOf)))))))

(tu/deftest-kb the-finding-says-inherited-rather-than-declared
  ;; "declared with 2 arguments" is false of a predicate nobody declared, and an author
  ;; reading it would go looking for a declaration on `fatherOf` that does not exist.
  (tu/with-terms [parentOf fatherOf A B C]
    (v/assert kb (list 'arity parentOf 2) 'CxUniverse)
    (v/assert kb (list fatherOf A B C) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (let [m (:message (get (arity-findings kb) fatherOf))]
      (is (re-find (re-pattern (str "takes 2 arguments through " parentOf)) m))
      (is (not (re-find #"is declared with" m))))))

(tu/deftest-kb the-undescended-finding-still-says-declared
  ;; The wording splits on `:via`, so the case that has no super must be untouched.
  (tu/with-terms [parentOf A B C]
    (v/assert kb (list parentOf A B C) 'CxUniverse)
    (v/assert kb (list 'arity parentOf 2) 'CxUniverse)
    (let [e (get (arity-findings kb) parentOf)]
      (is (= parentOf (:via e)) "read off itself")
      (is (re-find #"is declared with 2 arguments" (:message e))))))

(tu/deftest-kb a-wrong-arity-fact-is-refused-or-reported-in-every-arrival-order
  ;; The order-independence claim, stated as the property rather than as six cases.
  ;; Which of the two happens is first-writer-wins and *may* differ by order: a tuple
  ;; written onto a KB that already binds its predicate never lands, and one written
  ;; before the binding exists lands and is reported.  What may not differ is that the
  ;; KB ends up holding a wrong-arity fact nobody was told about.
  (doseq [order (orderings [:edge :declaration :tuple])]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [parentOf fatherOf A B C]
        (let [step    {:edge        #(v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
                       :declaration #(v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
                       :tuple       #(v/assert kb (list fatherOf A B C) 'CxUniverse)}
              refused (atom nil)]
          (doseq [s order]
            (when (= :arity (ex-type (step s))) (reset! refused s)))
          (let [stored?   (v/ask? kb (list fatherOf A B C) 'CxUniverse)
                reported? (contains? (arity-findings kb) fatherOf)]
            (is (or (= :tuple @refused) stored?)
                (str "the tuple is refused or it is stored, under " (pr-str order)))
            (is (not (and stored? (not reported?)))
                (str "a stored wrong-arity fact is always reported, under "
                     (pr-str order)))))))))

(tu/deftest-kb a-variableArity-super-files-nothing-either
  ;; The exemption is read by one `arity-problem`, and the retroactive path asks the same
  ;; one — so widening the trigger must not have opened a route around it.
  (tu/with-terms [chainOf subChainOf A B C]
    (v/assert kb (list 'binary_predicate chainOf) 'CxUniverse)
    (v/assert kb (list 'variable_arity chainOf) 'CxUniverse)
    (v/assert kb (list subChainOf A B C) 'CxUniverse)
    (v/assert kb (list 'genl subChainOf chainOf) 'CxUniverse)
    (is (empty? (arity-findings kb)))))

(tu/deftest-kb an-edge-under-a-predicate-nobody-declared-files-nothing
  ;; `genl` is the commonest edge in any KB, so the arm must cost a KB nothing when
  ;; there is no length above the edge to inherit.
  (tu/with-terms [parentOf fatherOf A B C]
    (v/assert kb (list fatherOf A B C) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (is (empty? (arity-findings kb)))))

;; ---- and the ingredient that names no predicate at all -------------------
;;
;; A binding is read **from a context**: `checks/declared-arity` filters the arity table
;; by the reader's `genlCx` ancestor set and reads the predicate-type membership through a
;; context-scoped reader.  So a `genlCx` edge rebinds a predicate exactly as a `genl` edge
;; does — the same three ingredients with a fourth deciding who can see them — and the
;; entry point answers it for free, because the entry point reads `declared-arity` whichever sentence
;; arrives.  The retroactive half cannot: a context edge names two contexts and no
;; predicate, so what it convicts has to be worked out from its two ends.  The order the
;; entry point cannot cover is the fact stored where nothing binds it, with the edge that binds
;; it arriving last.

(tu/deftest-kb a-context-edge-arriving-last-reports-the-facts-it-newly-convicts
  ;; The declaration is out of sight while the tuple is written, so the entry point cannot
  ;; refuse it; the visibility edge is what makes it wrong.
  (tu/with-terms [CxUp CxDown parentOf A B C]
    (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) CxUp)
    (v/assert kb (list parentOf A B C) CxDown)
    (is (empty? (arity-findings kb)) "CxDown cannot see the declaration yet")
    (v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
    (let [e (get (arity-findings kb) parentOf)]
      (is (some? e) "the visibility edge files the finding")
      (is (= 2 (:expected e)))
      (is (= [(list parentOf A B C)] (:sample e)))
      (is (v/ask? kb (list parentOf A B C) CxDown)
          "reported, not withdrawn — a visibility edge moves no belief either"))))

(tu/deftest-kb a-context-edge-that-reveals-an-inherited-length-reports-too
  ;; The other half of the same fourth ingredient: what the edge brings into sight is the
  ;; `genl` edge the length is inherited *through*, and the convicted predicate is named
  ;; by nothing in the ancestor set above — only by the fact itself.
  (tu/with-terms [CxUp CxDown parentOf fatherOf A B C]
    (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) CxUp)
    (v/assert kb (list 'genl fatherOf parentOf) CxUp)
    (v/assert kb (list fatherOf A B C) CxDown)
    (is (empty? (arity-findings kb)) "neither the length nor the edge is visible yet")
    (v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
    (let [e (get (arity-findings kb) fatherOf)]
      (is (some? e) "the finding is about the predicate whose facts are wrong")
      (is (= parentOf (:via e)) "and the length was read off the super, through the edge"))))

(tu/deftest-kb a-context-edge-arriving-first-refuses-at-the-entry-point
  ;; The control: the same three sentences in the order the entry point can see.  Refused *or*
  ;; reported is the property, and this is the refused side of it — the pair above is the
  ;; reported one, so a reader meets both halves of the asymmetry in one place.
  (tu/with-terms [CxUp CxDown parentOf A B C]
    (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) CxUp)
    (v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
    (is (= :arity (ex-type #(v/assert kb (list parentOf A B C) CxDown)))
        "the entry point reads the declaration through the visibility edge")
    (is (empty? (arity-findings kb))
        "and nothing was stored for the report to name")))

(tu/deftest-kb a-wrong-arity-fact-across-a-visibility-edge-is-refused-or-reported
  ;; The property, over every order of the three sentences — the `genlCx` twin of the
  ;; `genl` case above, and the statement that the asymmetry between the two axes is
  ;; gone.  Which of refusal and report happens still depends on the order; that the KB
  ;; ends up holding a wrong-arity fact nobody was told about may not.
  (doseq [order (orderings [:ctx-edge :declaration :tuple])]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [CxUp CxDown parentOf A B C]
        (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
        (let [step    {:ctx-edge    #(v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
                       :declaration #(v/assert kb (list 'binary_predicate parentOf) CxUp)
                       :tuple       #(v/assert kb (list parentOf A B C) CxDown)}
              refused (atom nil)]
          (doseq [s order]
            (when (= :arity (ex-type (step s))) (reset! refused s)))
          (let [stored?   (v/ask? kb (list parentOf A B C) CxDown)
                reported? (contains? (arity-findings kb) parentOf)]
            (is (or (= :tuple @refused) stored?)
                (str "the tuple is refused or it is stored, under " (pr-str order)))
            (is (not (and stored? (not reported?)))
                (str "a stored wrong-arity fact is always reported, under "
                     (pr-str order)))))))))

(tu/deftest-kb a-context-edge-is-swept-from-whichever-end-is-smaller
  ;; The reach has two ends and either one answers, so the pass walks the smaller: the
  ;; facts below `sub`, or the bindings above `super`.  Here the first is the whole loaded
  ;; KB and the second is one sentence, which is the form the shipped ontology writes —
  ;; `(genlCx CxUniverse CxMeasure)` attaches a root context to a vocabulary.
  (tu/with-terms [CxVocab parentOf A B C]
    (v/assert kb (list 'binary_predicate parentOf) CxVocab)
    (v/assert kb (list parentOf A B C) 'CxUniverse)
    (is (empty? (arity-findings kb)) "CxUniverse cannot see the declaration yet")
    (v/assert kb (list 'genlCx 'CxUniverse CxVocab) 'CxUniverse)
    (let [e (get (arity-findings kb) parentOf)]
      (is (some? e) "the edge is swept from the end that holds the binding")
      (is (= 2 (:expected e)))
      (is (= [(list parentOf A B C)] (:sample e))))))

(tu/deftest-kb a-context-edge-over-a-predicate-nobody-declared-files-nothing
  ;; `genlCx` is written once per context in any KB, so the arm must added no work where
  ;; there is no length in the ancestor set it opened.
  (tu/with-terms [CxUp CxDown parentOf A B C]
    (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
    (v/assert kb (list parentOf A B C) CxDown)
    (v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
    (is (empty? (arity-findings kb)))))

;; ---- and it says so when the budget stops it -----------------------------
;;
;; The sweep is over a **subtree** now, not one posting list, so the budget can run out
;; with predicates still to look at — and the flag rode on a *finding*, so a predicate
;; that spent the budget convicting nothing took the flag with it and every predicate
;; after it was examined zero facts deep in silence.  A wrong-arity fact under one of
;; them was then neither refused nor reported nor counted, which is the single thing
;; this pass may not do.

(defn- truncation
  "The `:arity-truncated` entry, or nil."
  [kb]
  (first (filter #(= :arity-truncated (:violation %)) (v/violations kb))))

(tu/deftest-kb the-budget-running-out-on-an-innocent-predicate-is-still-said-out-loud
  ;; The exact silent case: `aaa…` spends the budget and convicts nothing, so there is no
  ;; entry to carry `:truncated`; `zzz…` sorts after it, holds the wrong-length fact, and
  ;; is swept zero facts deep.
  (binding [tax/*exposure-instance-budget* 4]
    (tu/with-terms [parentOf A B C]
      (let [aaa (symbol (str "aaa" (name parentOf)))
            zzz (symbol (str "zzz" (name parentOf)))]
        (dotimes [i 5]
          (v/assert kb (list aaa A (symbol (str "TmpBud" i))) 'CxUniverse))
        (v/assert kb (list zzz A B C) 'CxUniverse)
        (v/assert kb (list 'genl aaa parentOf) 'CxUniverse)
        (v/assert kb (list 'genl zzz parentOf) 'CxUniverse)
        ;; the binding arrives last, so one pass sweeps both subtrees
        (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
        (is (v/ask? kb (list zzz A B C) 'CxUniverse)
            "the wrong-length fact is stored and believed, as it was before the binding")
        (is (empty? (arity-findings kb))
            "the premise: not one predicate convicts anything, so no finding can carry it")
        (let [t (truncation kb)]
          (is (some? t) "and the pass says a predicate went unswept rather than nothing")
          (is (pos? (get-in t [:detail :predicates])))
          (is (= [aaa zzz] (get-in t [:detail :sample]))
              "naming both — the one that spent the budget and the one that got none")
          (is (= 4 (get-in t [:detail :budget])))
          (is (re-find #"went unswept" (get-in t [:detail :message]))))
        ;; ...and a cut is not the cap, which is the other direction of the pin
        ;; `a-wide-subtree-cannot-file-its-way-through-the-ledger` makes.  The two say
        ;; opposite things to a reader — *not looked at* against *looked at and
        ;; summarized* — so a notice answering to both bounds would tell them one while
        ;; meaning the other.
        (is (empty? (filter #(= :arity-report-truncated (:violation %)) (v/violations kb)))
            "nothing convicted, so nothing overflowed the entry cap")))))

(tu/deftest-kb the-budget-running-out-on-a-context-edge-is-still-said-out-loud
  ;; The **fourth ingredient's** own cut, and the same silence one step earlier: a
  ;; `genlCx` edge names no predicate, so a budget spent inside the ancestor set it opened leaves
  ;; predicates the pass never got as far as naming.  None of them reaches `preds`, so no
  ;; sweep runs, nothing convicts, and the only thing that can say the pass was bounded
  ;; is the edge cut itself.
  ;;
  ;; `CxVocab` is a root context holding six bindings and no facts, so it is the smaller
  ;; end and the one walked (`a-context-edge-is-swept-from-whichever-end-is-smaller` is
  ;; the same shape) — and the predicates it binds hold nothing for a subtree walk to
  ;; read, which is what leaves `:predicates` at zero.
  (binding [tax/*exposure-instance-budget* 2]
    (tu/with-terms [CxVocab CxDown plainOf]
      (dotimes [_ 40]
        (v/assert kb (list plainOf (tu/tmp-ind "Subj") (tu/tmp-ind "Obj")) CxDown))
      (doseq [i (range 6)]
        (v/assert kb (list 'binary_predicate (tu/tmp-pred (str "vocab" i))) CxVocab))
      (v/clear-violations! kb)
      (v/assert kb (list 'genlCx CxDown CxVocab) 'CxUniverse)
      (is (empty? (arity-findings kb))
          "the premise: no predicate the edge binds holds a fact, so nothing convicts")
      (let [t (truncation kb)]
        (is (some? t) "and the pass says a context edge went unswept rather than nothing")
        (is (= 1 (get-in t [:detail :edges])))
        (is (= [(list 'genlCx CxDown CxVocab)] (get-in t [:detail :edge-sample]))
            "naming the edge whose ancestor set it did not finish")
        (is (zero? (get-in t [:detail :predicates]))
            "and no predicate sweep was cut, there being none to run")
        (is (= 2 (get-in t [:detail :budget])))
        (is (re-find #"genlCx edge\(s\) went unswept" (get-in t [:detail :message]))))
      (is (empty? (filter #(= :arity-report-truncated (:violation %)) (v/violations kb)))
          "and a cut is not the cap: nothing convicted, so nothing overflowed it"))))

(tu/deftest-kb a-stored-wrong-arity-fact-is-reported-or-the-cut-is
  ;; The property the pass owes, stated over both sides of the budget: a fact the entry point
  ;; could not have refused is named, or the reader is told the sweep did not reach it.
  ;; Never neither.
  (doseq [budget [4 4096]]
    (binding [tax/*exposure-instance-budget* budget]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [parentOf A B C]
          (let [aaa (symbol (str "aaa" (name parentOf)))
                zzz (symbol (str "zzz" (name parentOf)))]
            (dotimes [i 5]
              (v/assert kb (list aaa A (symbol (str "TmpBud" i))) 'CxUniverse))
            (v/assert kb (list zzz A B C) 'CxUniverse)
            (v/assert kb (list 'genl aaa parentOf) 'CxUniverse)
            (v/assert kb (list 'genl zzz parentOf) 'CxUniverse)
            (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
            (is (or (contains? (arity-findings kb) zzz) (some? (truncation kb)))
                (str "reported or declared cut, under budget " budget))
            (when (= 4096 budget)
              (is (contains? (arity-findings kb) zzz)
                  "and with budget to spare it is reported rather than excused")
              (is (nil? (truncation kb))
                  "a sweep that finished files no cut notice"))))))))

(tu/deftest-kb the-cut-is-one-entry-for-the-pass-naming-a-sample
  ;; `expose-clashes!`' reading, for its reason: past the cut the predicates are dropped
  ;; by arithmetic rather than by anything about themselves, so a per-predicate entry
  ;; would say one fact about the settle once per predicate.
  (binding [tax/*exposure-instance-budget* 1]
    (tu/with-terms [parentOf A B C]
      (let [subs (mapv #(symbol (str "sub" % (name parentOf))) (range 6))]
        (doseq [s subs]
          (v/assert kb (list s A B C) 'CxUniverse)
          (v/assert kb (list 'genl s parentOf) 'CxUniverse))
        (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
        (let [cut (filter #(= :arity-truncated (:violation %)) (v/violations kb))]
          (is (= 1 (count cut)) "one entry between them, not one each")
          (is (<= (count (get-in (first cut) [:detail :sample])) 3)
              "a sample rather than the whole list")
          (is (every? (set subs) (get-in (first cut) [:detail :sample]))
              "and the sample names predicates that really went unswept"))))))

(tu/deftest-kb a-sweep-that-fits-files-no-cut-notice
  ;; The gate on the entry is the cut, not the finding — so an ordinary retroactive
  ;; report must not start carrying one.
  (tu/with-terms [parentOf fatherOf A B C]
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list fatherOf A B C) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (is (contains? (arity-findings kb) fatherOf) "the finding is filed")
    (is (nil? (truncation kb)) "and nothing claims the sweep was bounded")))

;; ---- and how many entries the findings themselves may be ----------------
;;
;; The sweep is over a subtree, so the number of *findings* is bounded by the vocabulary
;; rather than by the trigger: one binding landing on a super convicts every predicate
;; under it that holds a wrong-length fact.  The ledger keeps the newest 1,000 entries and
;; logs each at `:warn`, so a pass filing one per predicate lets a single settle evict
;; every other violation in it — which is what the cap and its one overflow entry are for.

(tu/deftest-kb a-wide-subtree-cannot-file-its-way-through-the-ledger
  ;; Twenty predicates, one wrong-length fact each, one binding above all of them.
  (tu/with-terms [parentOf A B C]
    (let [subs (mapv #(symbol (str "sub" (format "%02d" %) (name parentOf))) (range 20))]
      (doseq [s subs]
        (v/assert kb (list s A B C) 'CxUniverse)
        (v/assert kb (list 'genl s parentOf) 'CxUniverse))
      (v/clear-violations! kb)
      (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
      (let [entries (v/violations kb)
            found   (filterv #(= :arity (:violation %)) entries)
            over    (filterv #(= :arity-report-truncated (:violation %)) entries)
            named   (set (map #(get-in % [:detail :predicate]) found))]
        (is (= 8 (count found)) "the findings are capped rather than one per predicate")
        (is (>= 10 (count entries)) "so one settle cannot evict a ledger of a thousand")
        (is (= 1 (count over)) "and the overflow is one entry, not one apiece")
        (testing "which says how many convicted, and how many facts between them"
          (is (= 20 (get-in (first over) [:detail :predicates])))
          (is (= 20 (get-in (first over) [:detail :facts])))
          (is (= 8 (get-in (first over) [:detail :filed]))))
        (testing "and names some of the predicates no entry names"
          (let [sample (get-in (first over) [:detail :sample])]
            (is (= 3 (count sample)))
            (is (every? (set subs) sample))
            (is (empty? (filter named sample)))))
        (is (nil? (truncation kb))
            "the cap is not a cut — every one of the twenty was swept and examined")))))

(tu/deftest-kb the-findings-under-the-cap-are-filed-whole
  ;; The cap may not cost an entry its content: under it the report is one whole entry
  ;; per convicted predicate, and no overflow notice.
  (tu/with-terms [parentOf A B C]
    (let [subs (mapv #(symbol (str "few" % (name parentOf))) (range 3))]
      (doseq [s subs]
        (v/assert kb (list s A B C) 'CxUniverse)
        (v/assert kb (list 'genl s parentOf) 'CxUniverse))
      (v/clear-violations! kb)
      (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
      (is (= (set subs) (set (keys (arity-findings kb))))
          "one entry per convicted predicate, while there is room for them")
      (is (empty? (filter #(= :arity-report-truncated (:violation %)) (v/violations kb)))
          "and nothing claims the report was bounded")
      (let [e (get (arity-findings kb) (first subs))]
        (is (= 2 (:expected e)))
        (is (= parentOf (:via e)))
        (is (= 1 (:count e)))
        (is (some? (:declared-after e)) "pointing at the declaration that convicted")
        (is (false? (:truncated e)))))))

;; ---- and the retroactive halves of the other two marks ------------------
;;
;; `functional` and `asymmetric` convict at the entry point through every mark **above** a
;; fact's own functor, which is what the two sections higher up pin: whichever spelling
;; arrives second is refused.  Each also has a **retroactive** half — the deciding sweep
;; `settle/declaration-implicates` runs under either constraint policy — and that half
;; has to descend too, or the mark descends at the entry point and nowhere else and the
;; same knowledge lands on a dilemma or on two coexisting claims according to which
;; sentence was written first.
;; Reading the extent of the predicate the declaration named is what does not descend: a
;; general spelling usually holds no facts of its own, so that reading is silent in
;; exactly the two orders the descension creates — the declaration landing on the super,
;; and the `genl` edge landing last.
;;
;; The cross-context half is `exposure-test`'s, the entry point seeing a same-context
;; pair whole and refusing it.  This is the same sweep asked of a co-located pair.

(defn- kinds
  "The kinds of the represented contradictions, in report order."
  [kb]
  (mapv :kind (v/contradictions kb)))

(tu/deftest-kb a-declaration-landing-on-the-super-reaches-the-sub-predicates-facts-too
  ;; The exact analogue of the `arity` case above, for the mark: `measureOf` holds no
  ;; facts and `birthYearOf` holds the clashing pair, so a sweep reading the named
  ;; predicate's own posting list looks at nothing at all.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [birthYearOf measureOf Tom]
      (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
      (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
      (is (empty? (kinds kb)) "nothing above birthYearOf says one value only, yet")
      (v/assert kb (list 'functional measureOf) 'CxUniverse)
      (is (= [:functional] (kinds kb))
          "the declaration reaches the facts of the subtree beneath it")
      (testing "and what is reported is the two stored fillers, ordered by content"
        (is (= (list 'contradicts
                     (list birthYearOf Tom 1980) (list birthYearOf Tom 1990))
               (:sentence (first (v/contradictions kb)))))))))

(tu/deftest-kb an-edge-carrying-a-standing-mark-down-reaches-them-as-well
  ;; The third ingredient, the one `arity` has too: the mark and the facts were both in
  ;; place and unrelated, and the edge is what put the second under the first.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [birthYearOf measureOf Tom]
      (v/assert kb (list 'functional measureOf) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
      (is (empty? (kinds kb)) "the mark is above nothing these facts are under")
      (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
      (is (= [:functional] (kinds kb)) "the edge is what makes them one slot's fillers"))))

(tu/deftest-kb a-descended-asymmetric-mark-reaches-back-the-same-way
  ;; The converse probe already fanned down the hierarchy and the mark now descends it,
  ;; so the retroactive half has both halves of the same question rather than one.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [muchLargerThan largerThan Rex Pip]
      (v/assert kb (list muchLargerThan Rex Pip) 'CxUniverse)
      (v/assert kb (list muchLargerThan Pip Rex) 'CxUniverse)
      (v/assert kb (list 'genl muchLargerThan largerThan) 'CxUniverse)
      (is (empty? (kinds kb)) "a relation nobody has declared one-way, held both ways")
      (v/assert kb (list 'asymmetric largerThan) 'CxUniverse)
      (is (= [:asymmetric] (kinds kb))))))

(tu/deftest-kb an-edge-under-no-marked-predicate-arbitrates-nothing
  ;; `genl` is the commonest edge in any KB, so the arm must added no work where there is
  ;; no mark above the edge to carry down — and must not start convicting a pair that
  ;; nothing declares anything about.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [birthYearOf measureOf otherOf Tom]
      (v/assert kb (list 'functional otherOf) 'CxUniverse)   ; marked, and unrelated
      (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
      (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
      (is (empty? (kinds kb)) "nothing marked is above either end of the edge"))))

(tu/deftest-kb a-descended-mark-answers-the-same-as-an-undescended-one-and-as-the-entry-point
  ;; The three arrangements that always worked, beside the one that did not — so the
  ;; asymmetry being gone is readable in one place rather than inferable from a passing
  ;; test elsewhere.  One KB shape four times, differing only in where the mark sits and
  ;; which sentence arrives last.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [birthYearOf measureOf Tom]
      (let [run  (fn [steps]
                   (tu/with-neutral-kb [k tu/isolated-fresh]
                     (doseq [s steps] (s k))
                     (kinds k)))
            f1   #(v/assert % (list birthYearOf Tom 1980) 'CxUniverse)
            f2   #(v/assert % (list birthYearOf Tom 1990) 'CxUniverse)
            flat #(v/assert % (list 'functional birthYearOf) 'CxUniverse)
            decl #(v/assert % (list 'functional measureOf) 'CxUniverse)
            edge #(v/assert % (list 'genl birthYearOf measureOf) 'CxUniverse)]
        (is (= [:functional] (run [f1 f2 flat]))
            "flat: the mark on the facts' own predicate")
        (is (= [:functional] (run [decl edge f1 f2]))
            "the entry point, which read the mark up the hierarchy all along")
        (is (= [:functional] (run [f1 f2 edge decl]))
            "the sweep, with the declaration last")
        (is (= [:functional] (run [decl f1 f2 edge]))
            "and the sweep, with the edge last")))))

(tu/deftest-kb every-arrival-order-of-a-descended-functional-clash-is-arbitrated
  ;; The order-independence claim as the property rather than as four cases.  Unlike the
  ;; `arity` property beside it there is no refused-or-reported split to make: under
  ;; `:arbitrate` nothing is refused, so all six orders of the pair of facts, the
  ;; declaration and the edge must land on the same represented dilemma.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [birthYearOf measureOf Tom]
      (doseq [order (orderings [:facts :declaration :edge])]
        (tu/with-neutral-kb [k tu/isolated-fresh]
          (let [step {:facts       #(do (v/assert k (list birthYearOf Tom 1980) 'CxUniverse)
                                        (v/assert k (list birthYearOf Tom 1990) 'CxUniverse))
                      :declaration #(v/assert k (list 'functional measureOf) 'CxUniverse)
                      :edge        #(v/assert k (list 'genl birthYearOf measureOf)
                                              'CxUniverse)}]
            (doseq [s order] ((step s)))
            (is (= [:functional] (kinds k))
                (str "arbitrated under " (pr-str order)))))))))

(tu/deftest-kb every-arrival-order-of-a-descended-asymmetric-clash-is-arbitrated
  ;; The same property for the other mark, and it is a second test rather than a second
  ;; arm: a clash reported once is reported until its ingredients move, so a second
  ;; scenario in one KB would read the first one's answer.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [muchLargerThan largerThan Rex Pip]
      (doseq [order (orderings [:facts :declaration :edge])]
        (tu/with-neutral-kb [k tu/isolated-fresh]
          (let [step {:facts       #(do (v/assert k (list muchLargerThan Rex Pip) 'CxUniverse)
                                        (v/assert k (list muchLargerThan Pip Rex) 'CxUniverse))
                      :declaration #(v/assert k (list 'asymmetric largerThan) 'CxUniverse)
                      :edge        #(v/assert k (list 'genl muchLargerThan largerThan)
                                              'CxUniverse)}]
            (doseq [s order] ((step s)))
            (is (= [:asymmetric] (kinds k))
                (str "arbitrated under " (pr-str order)))))))))
