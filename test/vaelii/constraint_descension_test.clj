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
  `the-walk-reads-hops-through-the-subsumption-fan` assert that, and nothing here may move
  them."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defmacro with-entailing
  "Run the body with assertive argument types on — off by default, so the minting half
  of every entry-point-parity pair binds it."
  [& body]
  `(binding [argument/*assertive-arg-types?* true] ~@body))

(defn- ex-type
  "The `:type` a write thunk meets: the ex-info it throws, or the argument conviction its
  fact is held inert under (`tu/write-type`), or nil.  Named rather
  than `(thrown? ExceptionInfo …)`: a descension collapsing into a naming or arity
  refusal is exactly the regression a bare `thrown?` stays green through."
  [f]
  (tu/write-type tu/*kb* f))

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

;; ---- entry point parity: the conviction ---------------------------------------

(tu/deftest-kb both-spellings-of-one-ill-typed-claim-are-held
  ;; The headline.  Without the descension the second assert stores a believed fact that
  ;; answers the very query the first one was held inert for.
  ;; Forced to the constraint reading: what descends is asserted here as a *conviction* of both
  ;; spellings, and with the entailment on a symbol argument is minted rather than convicted
  ;; (docs/argtypes.md).  The declaration read through the edge is the subject either way —
  ;; the entailment descends through the same edges, and argtype_entail_test holds that half.
  (tu/without-entailing
   (tu/with-terms [person rock parentOf fatherOf TheRock1 Mary]
     (a-type kb person 'CxUniverse)
     (a-type kb rock 'CxUniverse)
     (v/assert kb (list 'disjoint person rock) 'CxUniverse)
     (v/assert kb (list rock TheRock1) 'CxUniverse)
     (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
     (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
     (is (= :arg-type (ex-type #(v/assert kb (list parentOf TheRock1 Mary) 'CxUniverse)))
         "the declaration's own predicate")
     (is (= :arg-type (ex-type #(v/assert kb (list fatherOf TheRock1 Mary) 'CxUniverse)))
         "and the sub-predicate, whose tuples are the same tuples")
     (testing "the conviction names the predicate the constraint was declared of"
       (is (re-find (re-pattern (str "declared of " parentOf))
                    (:message (tu/write-conviction kb (list fatherOf TheRock1 Mary)
                                                   'CxUniverse)))))
     (testing "and a well-typed claim under either spelling still stores"
       (tu/with-terms [Fred]
         (v/assert kb (list person Fred) 'CxUniverse)
         (is (v/assert kb (list parentOf Fred Mary) 'CxUniverse))
         (is (v/assert kb (list fatherOf Fred Mary) 'CxUniverse)))))))

(tu/deftest-kb genlArg-descends-on-the-same-argument
  ;; the constraint-only reading: the conviction is the subject
  (tu/without-entailing
   (tu/with-terms [machine_t vehicle_t partType subPartType Rex]
     (a-type kb machine_t 'CxUniverse)
     (a-type kb vehicle_t 'CxUniverse)
     (v/assert kb (list 'disjoint machine_t vehicle_t) 'CxUniverse)
     (v/assert kb (list 'genl subPartType partType) 'CxUniverse)
     (v/assert kb (list 'genlArg partType 1 machine_t) 'CxUniverse)
     (is (= :arg-genl (ex-type #(v/assert kb (list partType vehicle_t Rex) 'CxUniverse)))
         "a kind the taxonomy separates from the declared type")
     (is (= :arg-genl (ex-type #(v/assert kb (list subPartType vehicle_t Rex) 'CxUniverse)))
         "and the same kind under the sub-predicate"))))

(tu/deftest-kb interArg-descends-by-riding-the-same-reader
  ;; the constraint-only reading: the conviction is the subject
  (tu/without-entailing
   (tu/with-terms [carnivore meat plant eats gnawsOn Rex Chunk]
     (a-type kb carnivore 'CxUniverse)
     (a-type kb meat 'CxUniverse)
     (a-type kb plant 'CxUniverse)
     (v/assert kb (list 'disjoint meat plant) 'CxUniverse)
     (v/assert kb (list 'genl gnawsOn eats) 'CxUniverse)
     (v/assert kb (list 'interArg eats 1 carnivore 2 meat) 'CxUniverse)
     (v/assert kb (list carnivore Rex) 'CxUniverse)
     (v/assert kb (list plant Chunk) 'CxUniverse)
     (is (= :inter-arg-type (ex-type #(v/assert kb (list eats Rex Chunk) 'CxUniverse))))
     (is (= :inter-arg-type (ex-type #(v/assert kb (list gnawsOn Rex Chunk) 'CxUniverse))))
     (testing "and the trigger still has to be established under either spelling"
       (tu/with-terms [Nobody]
         (is (v/assert kb (list gnawsOn Nobody Chunk) 'CxUniverse)
             "an untyped eater leaves the conditional dormant"))))))

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
  ;; The `genl` edge is read from the writer's vantage, as the declaration and the
  ;; membership are.  Forced to the constraint reading: the vantage rule is stated here
  ;; as which context convicts.
  (tu/without-entailing
   (tu/with-terms [person rock parentOf fatherOf TheRock1 Mary CxLeft CxRight]
     (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
     (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
     (a-type kb person 'CxUniverse)
     (a-type kb rock 'CxUniverse)
     (v/assert kb (list 'disjoint person rock) 'CxUniverse)
     (v/assert kb (list rock TheRock1) 'CxUniverse)
     (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
     ;; the edge is asserted in a sibling context CxLeft cannot see
     (v/assert kb (list 'genl fatherOf parentOf) CxRight)
     (is (v/assert kb (list fatherOf TheRock1 Mary) CxLeft)
         "no visible edge, so no constraint descends")
     (is (= :arg-type (ex-type #(v/assert kb (list fatherOf TheRock1 Mary) CxRight)))
         "and where the edge is visible the constraint is"))))

;; ---- the three arrival orders ------------------------------------------

(tu/deftest-kb an-edge-arriving-after-the-facts-holds-the-fact-it-convicts
  ;; The edge arriving last is the family's third ingredient: `assert` of it does not
  ;; throw, and the settle holds the fact it convicts inert, as the fact arriving after
  ;; the edge is (docs/argtypes.md, "An argument that fails its declared type is held
  ;; inert").  Forced to the constraint reading, under which a separated argument is
  ;; convicted.
  (tu/without-entailing
   (tu/with-terms [person rock parentOf fatherOf TheRock1 Mary]
     (a-type kb person 'CxUniverse)
     (a-type kb rock 'CxUniverse)
     (v/assert kb (list 'disjoint person rock) 'CxUniverse)
     (v/assert kb (list rock TheRock1) 'CxUniverse)
     (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
     (let [fh (v/assert kb (list fatherOf TheRock1 Mary) 'CxUniverse)]
       (is (v/in? kb fh) "believed while no edge carries the declaration to it")
       (is (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
           "the edge is admitted, not refused for what it convicts")
       (is (not (v/in? kb fh)) "and the fact it convicts is held inert")
       (is (= [[(list fatherOf TheRock1 Mary) :arg-type]]
              (into [] (comp (filter #(= :inert-argument (:violation %)))
                             (map (juxt :sentence (comp :type :detail))))
                    (v/violations kb))))
       (testing "and the next such claim is held alike"
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
;; `transitiveInArg` is asserted by `inherit-test`'s `the-licence-stays-with-the-predicate-
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
;; length is held to what `parentOf` was declared with, and a reader decides a tuple that
;; breaks it (docs/taxonomy.md, "Arity").  It is also the strictest: the other constraints
;; narrow going down, so a sub-predicate may add to them, while a length cannot be
;; narrowed — so the hierarchy is read where the predicate binds nothing, and two related
;; predicates binding different lengths are a hard clash of their bindings.

(defn- believed-at?
  "Is `sentence`, stored in `ctx`, believed as `reader` reads it?"
  ([kb sentence ctx] (believed-at? kb sentence ctx ctx))
  ([kb sentence ctx reader]
   (let [h (v/handle-of kb sentence ctx)]
     (boolean (and h (v/believed? kb h reader))))))

(defn- descension-clashes
  "The members' sentences of every standing `:arity-descension` pair, as a set of sets.
  Both readings: with CxUniverse's forced-monotonic declarations the bindings are `:monotonic` and the
  pair is a hard clash in `conflicts`, and on a bare KB they are `:default` and the pair
  is a dilemma in `contradictions`."
  [kb]
  (into #{} (comp (filter #(= :arity-descension (:kind %)))
                  (map #(into #{} (map :sentence) (:sides %))))
        (concat (v/conflicts kb) (v/contradictions kb))))

(tu/deftest-kb an-undeclared-sub-predicate-takes-its-supers-arity
  (tu/with-terms [parentOf fatherOf A B C D]
    (let [decl (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)]
      (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
      (v/assert kb (list fatherOf A B) 'CxUniverse)
      (is (believed-at? kb (list fatherOf A B) 'CxUniverse) "the inherited length holds")
      (is (tu/stored-in-clash? kb (list fatherOf A B C) 'CxUniverse)
          "and a ternary fatherOf fact is a ternary parentOf tuple, read OUT")
      (testing "a :monotonic one is inert, its conflict grounded on the super's own declaration"
        (let [h (v/assert kb (list fatherOf A B D) 'CxUniverse {:strength :monotonic})
              r (first (filter #(contains? (:nogood %) h) (v/conflicts kb)))]
          (is (= :arity (:kind r)))
          (is (= [decl] (mapv :handle (:grounds r)))))))))

(tu/deftest-kb a-signature-on-the-sub-predicate-must-match-the-supers
  ;; What the edge asserts is why: `(genl fatherOf parentOf)` says every `fatherOf` tuple
  ;; **is** a `parentOf` tuple, and tuples of different lengths are not the same tuples.
  ;; Every member is forced-monotonic, so under CxUniverse the pair is a hard
  ;; clash: stored and reported whichever of its three sentences arrives last.
  (let [ingredients [:edge :super-declaration :sub-declaration]]
    (doseq [last-in ingredients]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [parentOf fatherOf]
          (let [sentence {:edge              (list 'genl fatherOf parentOf)
                          :super-declaration (list 'arity parentOf 2)
                          :sub-declaration   (list 'arity fatherOf 3)}]
            (doseq [s ingredients :when (not= s last-in)]
              (v/assert kb (sentence s) 'CxUniverse))
            (is (some? (v/assert kb (sentence last-in) 'CxUniverse))
                (str "stored with " (name last-in) " arriving last"))
            (is (= #{#{(list 'arity parentOf 2) (list 'arity fatherOf 3)}}
                   (descension-clashes kb))
                (str "and the two declarations are one standing pair, " (name last-in) " last"))
            (is (every? #(believed-at? kb (sentence %) 'CxUniverse) ingredients)
                "and all three stay believed")))))))

(tu/deftest-kb the-predicate-type-spelling-of-a-signature-must-match-too
  ;; Both spellings bind a length, so the clash reads both.
  (doseq [last-in [:edge :sub-declaration]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [parentOf fatherOf]
        (let [sentence {:edge            (list 'genl fatherOf parentOf)
                        :sub-declaration (list 'ternary_predicate fatherOf)}]
          (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
          (doseq [s [:edge :sub-declaration] :when (not= s last-in)]
            (v/assert kb (sentence s) 'CxUniverse))
          (v/assert kb (sentence last-in) 'CxUniverse)
          (is (= #{#{(list 'binary_predicate parentOf) (list 'ternary_predicate fatherOf)}}
                 (descension-clashes kb))
              (str "a standing pair with " (name last-in) " arriving last")))))))

(tu/deftest-kb an-inherited-length-is-a-check-and-not-an-answer
  ;; A predicate that binds nothing takes its super's length as a *check*, so `(arity
  ;; fatherOf ?n)` answers only what somebody wrote of `fatherOf`.
  (tu/with-terms [parentOf fatherOf A B]
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list fatherOf A B) 'CxUniverse)
    (is (believed-at? kb (list fatherOf A B) 'CxUniverse) "the inherited length binds the tuple")
    (is (empty? (v/ask kb (list 'arity fatherOf '?n) 'CxUniverse))
        "and is not preserved as a fact — nobody wrote an arity of fatherOf")
    (testing "a matching declaration of its own is one value and no clash"
      (v/assert kb (list 'arity fatherOf 2) 'CxUniverse)
      (is (= 1 (count (v/ask kb (list 'arity fatherOf '?n) 'CxUniverse))))
      (is (empty? (descension-clashes kb))))))

(tu/deftest-kb every-arrival-order-of-an-arity-clash-reads-the-same
  ;; In all 24 orders of the edge, the two declarations and a tuple the sub's own length
  ;; admits, the KB stores all four, believes the tuple, and reports the one pair.
  (let [readings
        (into #{}
              (for [order (orderings [:edge :super-declaration :sub-declaration :tuple])]
                (tu/with-neutral-kb [kb tu/isolated-fresh]
                  (tu/with-terms [parentOf fatherOf A B C]
                    (let [s {:edge              (list 'genl fatherOf parentOf)
                             :super-declaration (list 'binary_predicate parentOf)
                             :sub-declaration   (list 'ternary_predicate fatherOf)
                             :tuple             (list fatherOf A B C)}]
                      (doseq [k order] (v/assert kb (s k) 'CxUniverse))
                      [(into {} (map (fn [k] [k (believed-at? kb (s k) 'CxUniverse)])) (keys s))
                       (count (descension-clashes kb))])))))]
    (is (= #{[{:edge true :super-declaration true :sub-declaration true :tuple true} 1]}
           readings))))

(tu/deftest-kb an-undeclared-predicate-between-two-declared-ones-is-still-a-pair
  ;; A predicate that declares nothing is not a predicate that binds nothing: the
  ;; closure through it puts the ternary `grandOf` under the binary `parentOf`, so the two
  ;; declarations are a pair whichever edge arrives last.
  (doseq [[label edges] [[:lower-first [:f>p :g>f]]
                         [:upper-first [:g>f :f>p]]]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [parentOf fatherOf grandOf]
        (let [edge {:f>p (list 'genl fatherOf parentOf)
                    :g>f (list 'genl grandOf fatherOf)}]
          (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
          (v/assert kb (list 'ternary_predicate grandOf) 'CxUniverse)
          (doseq [e edges] (v/assert kb (edge e) 'CxUniverse))
          (is (= #{#{(list 'binary_predicate parentOf) (list 'ternary_predicate grandOf)}}
                 (descension-clashes kb))
              (str "the pair is reported, " (name label))))))))

(tu/deftest-kb every-arity-reader-reads-the-same-binding
  ;; One row per spelling of a binding, or of a near-miss.  A `:monotonic` membership binds
  ;; through `:monotonic` `genl` edges to an exact-arity class, and a `:default` membership
  ;; or edge on the path binds nothing (docs/taxonomy.md, "Arity").  Each row reads the
  ;; ternary tuple's belief, `admitsArgnum` at 2 and 3, `describe`'s `:arity` and the
  ;; `(arg P 3 thing)` check, with the binding before the tuple and after it.  The KB is
  ;; empty, so each row first states CxUniverse's two `:monotonic` edges the marks read.
  (let [m     {:strength :monotonic}
        bound [false [true false] 2 [:arg-position]]
        open  [true [false false] nil []]
        rows  {:binary_predicate  [(fn [_ _ p] [[(list 'binary_predicate p)]]) bound]
               :arity-2           [(fn [_ _ p] [[(list 'arity p 2)]]) bound]
               :kind-mark-mono    [(fn [_ _ p] [[(list 'instance_relation_predicate p) m]]) bound]
               :kind-mark-default [(fn [_ _ p] [[(list 'instance_relation_predicate p)]]) open]
               :functional-mono   [(fn [_ _ p] [[(list 'functional p) m]]) bound]
               ;; forced-monotonic, as CxUniverse declares it: the mark keeps the strength
               ;; it was written at, and a :default one binds nothing
               :functional        [(fn [_ _ p] [[(list 'forced_monotonic_predicate 'functional) m]
                                                [(list 'functional p)]])
                                   open]
               :default-edge      [(fn [k _ p] [[(list 'genl k 'binary_predicate)] [(list k p) m]]) open]
               :default-both      [(fn [k _ p] [[(list 'genl k 'binary_predicate)] [(list k p)]]) open]
               :two-lengths       [(fn [k j p] [[(list 'genl k 'binary_predicate) m] [(list k p) m]
                                                [(list 'genl j 'ternary_predicate) m] [(list j p) m]])
                                   open]}]
    (doseq [[label [ops want]] rows
            tuple-first? [false true]]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [rel_kind other_kind pairOf A B C]
          (let [tuple   (list pairOf A B C)
                binding #(doseq [[s o] (ops rel_kind other_kind pairOf)]
                           (v/assert kb s 'CxUniverse (or o {})))]
            (doseq [k '[instance_relation_predicate functional]]
              (v/assert kb (list 'genl k 'binary_predicate) 'CxUniverse m))
            (when-not tuple-first? (binding))
            (v/assert kb tuple 'CxUniverse)
            (when tuple-first? (binding))
            (is (= want
                   [(believed-at? kb tuple 'CxUniverse)
                    (mapv #(v/ask? kb (list 'admitsArgnum pairOf %) 'CxUniverse) [2 3])
                    (:arity (v/describe kb pairOf 'CxUniverse))
                    (mapv :type (v/check kb (list 'arg pairOf 3 'thing) 'CxUniverse))])
                (str (name label) (if tuple-first? ", tuple first" ", binding first")))))))))

(tu/deftest-kb supers-that-disagree-about-arity-bind-nothing
  ;; Unsettled is not the same as undeclared, and it constrains the same.
  (tu/with-terms [leftOf rightOf bothOf A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl bothOf leftOf) 'CxUniverse)
      (v/assert kb (list 'genl bothOf rightOf) 'CxUniverse)
      (v/assert kb (list 'arity leftOf 2) 'CxUniverse)
      (v/assert kb (list 'arity rightOf 3) 'CxUniverse))
    (v/assert kb (list bothOf A B) 'CxUniverse)
    (v/assert kb (list bothOf A B C) 'CxUniverse)
    (is (believed-at? kb (list bothOf A B) 'CxUniverse))
    (is (believed-at? kb (list bothOf A B C) 'CxUniverse)
        "no unanimous answer above it, so nothing binds")))

(tu/deftest-kb a-variableArity-super-releases-the-inheritance
  (tu/with-terms [chainOf subChainOf A B C]
    (v/assert kb (list 'binary_predicate chainOf) 'CxUniverse)
    (v/assert kb (list 'genl subChainOf chainOf) 'CxUniverse)
    (v/assert kb (list subChainOf A B C) 'CxUniverse)
    (is (not (believed-at? kb (list subChainOf A B C) 'CxUniverse)))
    (v/assert kb (list 'variable_arity chainOf) 'CxUniverse)
    (testing "a relation that reads a chain of any length binds nothing beneath it to one"
      (is (believed-at? kb (list subChainOf A B C) 'CxUniverse)))))

(tu/deftest-kb a-variableArity-super-releases-it-without-declaring-a-length-itself
  ;; A super marked `variable_arity` and given no length says the hierarchy under it reads
  ;; a chain, so it releases what a sibling's binary declaration would have bound.
  (tu/with-terms [chainOf otherOf subOf A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'variable_arity chainOf) 'CxUniverse)
      (v/assert kb (list 'binary_predicate otherOf) 'CxUniverse)
      (v/assert kb (list 'genl subOf chainOf) 'CxUniverse)
      (v/assert kb (list 'genl subOf otherOf) 'CxUniverse))
    (v/assert kb (list subOf A B C) 'CxUniverse)
    (is (believed-at? kb (list subOf A B C) 'CxUniverse))))

(tu/deftest-kb variable_arity-on-either-side-releases-the-match-across-the-edge
  ;; A relation that reads a chain of any length makes no claim about the length of the
  ;; tuples above or below it, so there is nothing for a second declaration to contradict.
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
          (v/assert kb (sentence last-in) 'CxUniverse)
          (is (empty? (descension-clashes kb))
              (str "released with the mark on the " (name marked)
                   " and " (name last-in) " last"))
          (v/assert kb (list subChainOf A B C) 'CxUniverse)
          (is (believed-at? kb (list subChainOf A B C) 'CxUniverse)
              "and the chain it exists to license is believed"))))))

;; ---- asymmetric --------------------------------------------------------
;;
;; The converse probe already fanned *down* the hierarchy; only the mark was read off the
;; exact functor.  So which spelling arrived second decided whether the pair was found.

(tu/deftest-kb an-asymmetric-super-convicts-a-sub-predicate-in-both-orders
  (doseq [order [:general-first :specialized-first]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [typeLargerThan muchLargerThan A B]
        (v/assert kb (list 'asymmetric typeLargerThan) 'CxUniverse)
        (v/assert kb (list 'genl muchLargerThan typeLargerThan) 'CxUniverse)
        (let [general #(v/assert kb (list typeLargerThan A B) 'CxUniverse {:strength :monotonic})
              special #(v/assert kb (list muchLargerThan B A) 'CxUniverse {:strength :monotonic})]
          (if (= order :general-first) (general) (special))
          ((if (= order :general-first) special general))
          (is (= [:asymmetric] (mapv :kind (v/conflicts kb)))
              (str "the converse is stored and the known-true pair is a conflict under "
                   (name order))))))))

(tu/deftest-kb the-asymmetry-violation-names-the-predicate-the-mark-is-on
  (tu/with-terms [typeLargerThan muchLargerThan A B]
    (v/assert kb (list 'asymmetric typeLargerThan) 'CxUniverse)
    (v/assert kb (list 'genl muchLargerThan typeLargerThan) 'CxUniverse)
    (v/assert kb (list muchLargerThan A B) 'CxUniverse {:strength :monotonic})
    (is (re-find (re-pattern (str "asymmetric: " typeLargerThan " cannot hold both ways"))
                 (:message (first (#'checks/asymmetry-problems
                                   kb (list muchLargerThan B A) 'CxUniverse)))))))

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
          f1 (v/assert kb (list birthMotherOf Tom lo) 'CxUniverse {:strength :monotonic})]
      (v/assert kb (list birthMotherOf Tom hi) 'CxUniverse {:strength :monotonic})
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
        (v/assert kb (list motherOf Tom lo) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list fatherOf Tom hi) 'CxUniverse {:strength :monotonic})
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
            (v/assert kb (list fatherOf Tom lo) 'CxUniverse {:strength :monotonic})
            (v/assert kb (list fatherOf Tom hi) 'CxUniverse {:strength :monotonic})
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
              (v/assert kb (list fatherOf Tom lo) 'CxUniverse {:strength :monotonic})
              (v/assert kb (list dadOf Tom hi) 'CxUniverse {:strength :monotonic})
              (is (v/same-class? kb lo hi) "both are parentOf tuples, so the pair merges")
              (let [as (antecedents kb lo hi)]
                (is (= 1 (count (filter #{ef} as))) "the shared hop, named once")
                (is (= 1 (count (filter #{ed} as))) "and the hop only one side takes")
                (is (= (count as) (count (distinct as)))))
              (testing "and each edge still carries the merge, deduped or not"
                (v/retract! kb ef)
                (is (not (v/same-class? kb lo hi))
                    "the shared hop is gone, so neither fact is a parentOf tuple")))))))))

(tu/deftest-kb a-descended-merge-over-two-routes-survives-either-route-going
  ;; `fatherOf` reaches the marked `parentOf` over two routes, through `dadOf` and
  ;; through `sireOf`.  The merge names one of them (`checks/edge-support`), so
  ;; retracting an edge on it deletes the justification and defeating one takes it OUT;
  ;; the other route still licenses the merge, and the removal or the defeat re-derives
  ;; it (`special/rederive-descended`).
  (let [results
        (for [mark ['functional 'anti_symmetric]
              how  [:retract :defeat]
              cut  [:dadOf :sireOf]]
          (tu/with-neutral-kb [kb tu/isolated-fresh]
            (tu/with-terms [parentOf fatherOf dadOf sireOf Tom]
              (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
                    ed (v/assert kb (list 'genl fatherOf dadOf) 'CxUniverse)
                    es (v/assert kb (list 'genl fatherOf sireOf) 'CxUniverse)]
                (v/assert kb (list 'genl dadOf parentOf) 'CxUniverse)
                (v/assert kb (list 'genl sireOf parentOf) 'CxUniverse)
                (v/assert kb (list mark parentOf) 'CxUniverse)
                (if (= 'functional mark)
                  (do (v/assert kb (list fatherOf Tom lo) 'CxUniverse {:strength :monotonic})
                      (v/assert kb (list fatherOf Tom hi) 'CxUniverse {:strength :monotonic}))
                  (do (v/assert kb (list fatherOf lo hi) 'CxUniverse {:strength :monotonic})
                      (v/assert kb (list fatherOf hi lo) 'CxUniverse {:strength :monotonic})))
                (let [before (v/same-class? kb lo hi)]
                  (if (= :retract how)
                    (v/retract! kb (if (= :dadOf cut) ed es))
                    (v/assert kb (list 'not (list 'genl fatherOf (if (= :dadOf cut) dadOf sireOf)))
                              'CxUniverse {:strength :monotonic}))
                  [mark how cut [before (v/same-class? kb lo hi)]])))))]
    (is (= #{[true true]} (set (map last results)))
        (str "a route's edge going un-merged the pair: "
             (pr-str (remove #(= [true true] (last %)) results))))))

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
      (v/assert kb (list motherOf Tom lo) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list fatherOf Tom hi) 'CxUniverse {:strength :monotonic})
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
              step {:f1   #(v/assert kb (list birthMotherOf Tom lo) 'CxUniverse {:strength :monotonic})
                    :f2   #(v/assert kb (list birthMotherOf Tom hi) 'CxUniverse {:strength :monotonic})
                    :decl #(v/assert kb (list 'functional motherOf) 'CxUniverse)
                    :edge #(v/assert kb (list 'genl birthMotherOf motherOf) 'CxUniverse)}]
          (doseq [s order] ((step s)))
          (is (v/same-class? kb lo hi) (str "merged under " (pr-str order))))))))

(tu/deftest-kb a-numeric-clash-under-a-descended-mark-is-a-nogood-not-a-merge
  ;; No merge can make two numbers one thing, so the descension carries the clash down
  ;; rather than the equality, and the violation names the marked predicate.
  (tu/with-terms [birthYearOf bornInYear Tom]
    (v/assert kb (list 'functional birthYearOf) 'CxUniverse)
    (v/assert kb (list 'genl bornInYear birthYearOf) 'CxUniverse)
    (v/assert kb (list bornInYear Tom 1980) 'CxUniverse)
    (is (re-find (re-pattern (str "functional violation: " birthYearOf))
                 (:message (first (#'checks/functional-problems
                                   kb (list bornInYear Tom 1990) 'CxUniverse)))))
    (is (tu/stored-in-clash? kb (list bornInYear Tom 1990) 'CxUniverse))
    (is (= [:functional] (mapv :kind (v/contradictions kb))))))

;; ---- what does not move ------------------------------------------------

(tu/deftest-kb a-declarations-own-checks-read-its-own-predicates-arity
  ;; `declaration-problem` runs on the declaration rather than on the content it
  ;; constrains, and it asks whether the *declaring* predicate has the position named.
  ;; The descension is about which tuples a declaration reaches, not about which
  ;; positions the predicate it names has.
  ;;
  ;; Two genl-related predicates of different lengths is a hard clash, so the pair that
  ;; makes the point is the one the rule exempts: `variable_arity` on the sub releases the
  ;; match, and the two lengths stand side by side to be read off separately.
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

;; ---- every arrival order reads the same --------------------------------
;;
;; A binding reaches a tuple through its own predicate's declaration, a super-predicate's
;; through a `genl` edge, and a relation's length is read the same at every context
;; (docs/taxonomy.md, "Arity"), so whichever of those arrives last, the tuple reads the
;; same.

(tu/deftest-kb a-wrong-arity-fact-reads-the-same-in-every-arrival-order
  (let [readings
        (into #{}
              (for [strength [:default :monotonic]
                    order    (orderings [:declaration :edge :tuple])]
                (tu/with-neutral-kb [kb tu/isolated-fresh]
                  (tu/with-terms [parentOf fatherOf A B C]
                    (let [tuple (list fatherOf A B C)
                          step  {:declaration #(v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
                                 :edge        #(v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
                                 :tuple       #(v/assert kb tuple 'CxUniverse {:strength strength})}]
                      (doseq [k order] ((step k)))
                      [strength
                       (believed-at? kb tuple 'CxUniverse)
                       (mapv (juxt :kind (comp count :grounds)) (v/conflicts kb))])))))]
    (is (= #{[:default false [[:arity 1]]] [:monotonic false [[:arity 1]]]} readings)
        "inert at either strength, in all six orders")))

(tu/deftest-kb a-binding-a-reader-does-not-see-holds-the-tuple-inert-there-in-every-order
  ;; The declaration is stated in a context the tuple's own does not see until the
  ;; `genlCx` edge arrives, and a reader beside the tuple's context never sees it: the
  ;; tuple is inert at both.
  (let [readings
        (into #{}
              (for [order (orderings [:declaration :edge :tuple])]
                (tu/with-neutral-kb [kb tu/isolated-fresh]
                  (tu/with-terms [pairOf CxLower CxUpper CxAside A B C]
                    (v/assert kb (list 'genlCx CxUpper 'CxUniverse) 'CxUniverse)
                    (v/assert kb (list 'genlCx CxAside 'CxUniverse) 'CxUniverse)
                    (v/assert kb (list 'genlCx CxLower CxAside) 'CxUniverse)
                    (let [tuple (list pairOf A B C)
                          step  {:declaration #(v/assert kb (list 'binary_predicate pairOf) CxUpper)
                                 :edge        #(v/assert kb (list 'genlCx CxLower CxUpper) 'CxUniverse)
                                 :tuple       #(v/assert kb tuple CxAside)}]
                      (doseq [k order] ((step k)))
                      [(believed-at? kb tuple CxAside CxLower)
                       (believed-at? kb tuple CxAside CxAside)])))))]
    (is (= #{[false false]} readings))))

;; ---- and the retroactive halves of the other two marks ------------------
;;
;; The deciding sweep (`settle/declaration-parts`) reaches the facts beneath a mark
;; on a super-predicate, whichever of the facts, the declaration and the `genl` edge
;; arrives last.  The cross-context half is `exposure_test`'s.

(defn- kinds
  "The kinds of the represented contradictions, in report order."
  [kb]
  (mapv :kind (v/contradictions kb)))

(tu/deftest-kb an-edge-under-no-marked-predicate-arbitrates-nothing
  (tu/with-terms [birthYearOf measureOf otherOf Tom]
    (v/assert kb (list 'functional otherOf) 'CxUniverse)   ; marked, and unrelated
    (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
    (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
    (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
    (is (empty? (kinds kb)) "nothing marked is above either end of the edge")))

(tu/deftest-kb every-arrival-order-of-a-descended-clash-is-arbitrated
  ;; each order in a fresh KB, since a reported clash stays reported until its
  ;; ingredients move
  (doseq [{:keys [kind mark facts]}
          [{:kind :functional :mark 'functional
            :facts (fn [p a _] [(list p a 1980) (list p a 1990)])}
           {:kind :asymmetric :mark 'asymmetric
            :facts (fn [p a b] [(list p a b) (list p b a)])}]]
    (tu/with-terms [subP superP A B]
      (let [readings
            (into []
                  (for [order (orderings [:facts :declaration :edge])]
                    (tu/with-neutral-kb [k tu/isolated-fresh]
                      (let [step {:facts       #(doseq [s (facts subP A B)]
                                                  (v/assert k s 'CxUniverse))
                                  :declaration #(v/assert k (list mark superP) 'CxUniverse)
                                  :edge        #(v/assert k (list 'genl subP superP)
                                                          'CxUniverse)}]
                        (doseq [s (butlast order)] ((step s)))
                        (let [before (kinds k)]
                          ((step (last order)))
                          [order before (kinds k)
                           (:sentence (first (v/contradictions k)))])))))]
        (doseq [[order before after] readings]
          (is (= [[] [kind]] [before after])
              (str (name kind) ", nothing before the last of " (pr-str order))))
        (is (= 1 (count (into #{} (map peek) readings)))
            (str (name kind) ": one report sentence in every order"))))))
