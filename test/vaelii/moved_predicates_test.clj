;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.moved-predicates-test
  "A `genl` edge re-joins the forward rules of the preserved predicates whose claims can
  reach across it, and no others (`inherit/moved-predicates`, `crossing-claim?`).

  Every declaration in a KB may preserve along `genl`, so an edge that re-joined all of
  their rules made K edges cost K² full re-joins.  The narrowing keeps a predicate when a
  claim on it, or on a sub-predicate, in either polarity, has its preserved argument
  below the edge's lower term or above its upper one, at every position a permuting mark
  lets the claim hold it at.  An edge whose closure is past `crossing-closure-cap` is not
  narrowed.  The unit cases read the selection; the order cases hold the conclusion a
  narrowed re-join must still find, in every arrival order, with the claim two or three
  edges from the edge that arrives."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- permutations [coll]
  (if (empty? coll)
    [[]]
    (mapcat (fn [x] (map #(vec (cons x %)) (permutations (remove #{x} coll)))) coll)))

(defn- terms
  "A fresh temporary for each symbol, keyed by the symbol."
  [syms]
  (zipmap syms (map #(tu/fresh-term (tu/term-role %) %) syms)))

(defn- chain!
  "`low → mid → high → thing`, a declaration preserving `rel`'s first argument along
  `genl`, and a claim on `rel` at `high` with `thing` at the unpreserved second argument."
  [kb rel low mid high]
  (doseq [t [low mid high]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
  (v/assert kb (list 'genl low mid) 'CxUniverse)
  (v/assert kb (list 'genl mid high) 'CxUniverse)
  (v/assert kb (list 'transitiveInArg rel 1 'genl) 'CxUniverse)
  (v/assert kb (list rel high 'thing) 'CxUniverse))

(tu/deftest-kb a-genl-edge-moves-the-predicates-whose-claims-cross-it
  (let [{:syms [aRel bRel cRel subRel symRel low_a mid_a high_a low_b mid_b high_b
                below_b far_u far_v]}
        (terms '[aRel bRel cRel subRel symRel low_a mid_a high_a low_b mid_b high_b
                 below_b far_u far_v])
        moved #(inherit/moved-predicates kb %)]
    (chain! kb aRel low_a mid_a high_a)
    (chain! kb bRel low_b mid_b high_b)
    (v/assert kb (list 'genl far_v 'thing) 'CxUniverse)
    (testing "a claim above the edge's upper term moves its predicate alone, although
              every claim holds `thing`, which is above every edge, at argument 2"
      (is (= #{aRel} (moved (list 'genl low_a mid_a))))
      (is (= #{bRel} (moved (list 'genl mid_b high_b)))))
    (testing "a defeat of the edge selects as the edge does"
      (is (= #{aRel} (moved (list 'not (list 'genl low_a mid_a))))))
    (testing "an edge below `thing` between terms no claim reaches moves nothing"
      (is (= #{} (moved (list 'genl far_u far_v)))))
    (testing "a claim below the edge's lower term"
      (v/assert kb (list 'genl below_b low_b) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg cRel 1 'genl) 'CxUniverse)
      (v/assert kb (list cRel below_b 'thing) 'CxUniverse)
      (is (= #{bRel cRel} (moved (list 'genl low_b mid_b))))
      (is (= #{aRel} (moved (list 'genl low_a mid_a)))))
    (testing "a claim on a sub-predicate moves the preserved predicate above it"
      (v/assert kb (list 'genl subRel aRel) 'CxUniverse)
      (v/assert kb (list subRel high_b 'thing) 'CxUniverse)
      (is (= #{aRel bRel cRel} (moved (list 'genl low_b mid_b)))))
    (testing "a denial is a claim"
      (v/assert kb (list 'not (list bRel high_a 'thing)) 'CxUniverse)
      (is (= #{aRel bRel} (moved (list 'genl low_a mid_a)))))
    (testing "a symmetric predicate's claim is read at both arguments"
      (v/assert kb (list 'transitiveInArg symRel 1 'genl) 'CxUniverse)
      (v/assert kb (list symRel far_u high_a) 'CxUniverse)
      (is (= #{aRel bRel} (moved (list 'genl low_a mid_a))))
      (v/assert kb (list 'symmetric symRel) 'CxUniverse)
      (is (= #{aRel bRel symRel} (moved (list 'genl low_a mid_a)))))
    (testing "a claim at `thing` on the preserved argument crosses every edge"
      (v/assert kb (list aRel 'thing 'thing) 'CxUniverse)
      (is (contains? (moved (list 'genl low_b mid_b)) aRel))
      ;; and `symRel`'s mirrored claim sits at `far_u` itself: either end of the edge is
      ;; kept whichever way the declaration reads the relation
      (is (= #{aRel symRel} (moved (list 'genl far_u far_v)))))))

;; ---- the conclusion a narrowed re-join must still find --------------------

(defn- far-claim
  "A claim three edges above the conclusion's term, on `rel` or on a sub-predicate of it,
  in one of `(permutations …)` of its arriving sentences after the declaration and rule."
  [variant]
  (let [{:syms [low_t mid_t high_t top_t val_t rel subRel noted]}
        (terms '[low_t mid_t high_t top_t val_t rel subRel noted])
        claim-on (if (= variant :sub) subRel rel)]
    {:base  (cond-> [[(list 'transitiveInArg rel 1 'genl) 'CxUniverse]
                     [(list 'set/forwardRule (list 'implies (list rel '?x '?y) (list noted '?x '?y)))
                      'CxUniverse]]
              (= variant :sub) (conj [(list 'genl subRel rel) 'CxUniverse]))
     :rest  [[(list 'genl low_t mid_t) 'CxUniverse]
             [(list 'genl mid_t high_t) 'CxUniverse]
             [(list 'genl high_t top_t) 'CxUniverse]
             [(list claim-on top_t val_t) 'CxUniverse]]
     :goals [(list noted low_t val_t) (list noted mid_t val_t) (list noted high_t val_t)]}))

(defn- reading [{:keys [base goals]} order]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (doseq [[s c] (concat base order)] (v/assert kb s c))
    (mapv #(v/ask? kb % 'CxUniverse) goals)))

(defn- holds-in-every-order [variant]
  (let [l (far-claim variant)]
    (doseq [order (permutations (:rest l))]
      (is (= [true true true] (reading l order))
          (str variant " " (pr-str (mapv first order)))))))

(deftest a-claim-three-edges-away-fires-whichever-edge-arrives-last
  (holds-in-every-order :direct))

(deftest a-sub-predicate-claim-three-edges-away-fires-whichever-edge-arrives-last
  (holds-in-every-order :sub))

;; ---- the permuting marks, the inverse form and the closure cap -------------

(defn- chain-of!
  "`low → mid → high`, each also under `thing`."
  [kb low mid high]
  (doseq [t [low mid high]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
  (v/assert kb (list 'genl low mid) 'CxUniverse)
  (v/assert kb (list 'genl mid high) 'CxUniverse))

(tu/deftest-kb a-commutative-claim-is-read-at-every-position
  (let [{:syms [comRel low_c mid_c high_c k_t far_u far_v]}
        (terms '[comRel low_c mid_c high_c k_t far_u far_v])
        moved #(inherit/moved-predicates kb %)]
    (chain-of! kb low_c mid_c high_c)
    (doseq [t [k_t far_u far_v]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (v/assert kb (list 'transitiveInArg comRel 1 'genl) 'CxUniverse)
    (v/assert kb (list comRel k_t high_c) 'CxUniverse)
    (testing "unmarked, the claim holds the edge's upper term at an unpreserved position"
      (is (= #{} (moved (list 'genl low_c mid_c)))))
    (testing "`(commutative P)` permutes every position, whatever the claim's arity, so
              every edge moves the predicate"
      (v/assert kb (list 'commutative comRel) 'CxUniverse)
      (is (= #{comRel} (moved (list 'genl low_c mid_c))))
      (is (= #{comRel} (moved (list 'genl far_u far_v)))))
    (testing "the mark's own arrival moves the predicate"
      (is (= #{comRel} (moved (list 'commutative comRel)))))))

(tu/deftest-kb a-commutative-in-args-claim-is-read-at-the-positions-it-names
  (let [{:syms [argRel supRel subRel low_d mid_d high_d k_t j_t far_u far_v]}
        (terms '[argRel supRel subRel low_d mid_d high_d k_t j_t far_u far_v])
        moved #(inherit/moved-predicates kb %)]
    (chain-of! kb low_d mid_d high_d)
    (doseq [t [k_t j_t far_u far_v]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (v/assert kb (list 'transitiveInArg argRel 1 'genl) 'CxUniverse)
    (v/assert kb (list 'commutativeInArgs argRel 1 2) 'CxUniverse)
    (testing "position 3 is outside the component, so a claim holding the term there
              does not cross"
      (v/assert kb (list argRel k_t j_t high_d) 'CxUniverse)
      (is (= #{} (moved (list 'genl low_d mid_d)))))
    (testing "position 2 shares position 1's component"
      (v/assert kb (list argRel k_t high_d j_t) 'CxUniverse)
      (is (= #{argRel} (moved (list 'genl low_d mid_d))))
      (is (= #{} (moved (list 'genl far_u far_v)))))
    (testing "a mark on a sub-predicate widens the reading of that sub-predicate's claims"
      (v/assert kb (list 'transitiveInArg supRel 1 'genl) 'CxUniverse)
      (v/assert kb (list 'genl subRel supRel) 'CxUniverse)
      (v/assert kb (list subRel k_t far_v j_t) 'CxUniverse)
      (is (= #{} (moved (list 'genl far_u far_v))))
      (v/assert kb (list 'commutativeInArgs subRel 2 1) 'CxUniverse)
      (is (= #{supRel} (moved (list 'genl far_u far_v)))))))

(tu/deftest-kb an-inverse-declaration-crosses-an-edge-above-its-claim
  (let [{:syms [invRel low_e mid_e high_e k_t far_u far_v]}
        (terms '[invRel low_e mid_e high_e k_t far_u far_v])
        moved #(inherit/moved-predicates kb %)]
    (chain-of! kb low_e mid_e high_e)
    (doseq [t [k_t far_u far_v]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (v/assert kb (list 'transitiveInArgInverse invRel 1 'genl) 'CxUniverse)
    (v/assert kb (list invRel low_e k_t) 'CxUniverse)
    (is (= #{invRel} (moved (list 'genl mid_e high_e))))
    (is (= #{invRel} (moved (list 'not (list 'genl low_e mid_e)))))
    (is (= #{} (moved (list 'genl far_u far_v))))))

(tu/deftest-kb an-edge-whose-closure-is-past-the-cap-moves-every-predicate-on-genl
  (let [{:syms [aRel bRel low_a mid_a high_a low_b mid_b high_b]}
        (terms '[aRel bRel low_a mid_a high_a low_b mid_b high_b])
        moved #(inherit/moved-predicates kb %)
        tx    (reasoning/taxonomy kb)]
    (chain! kb aRel low_a mid_a high_a)
    (chain! kb bRel low_b mid_b high_b)
    (let [n (+ (count (tax/specs-global tx low_a)) (count (tax/genls-global tx mid_a)))]
      (with-redefs [inherit/crossing-closure-cap n]
        (is (= #{aRel} (moved (list 'genl low_a mid_a)))
            "a closure at the cap is narrowed"))
      (with-redefs [inherit/crossing-closure-cap (dec n)]
        (is (= #{aRel bRel} (moved (list 'genl low_a mid_a)))
            "one term past it selects every predicate preserved along genl")
        (is (= #{aRel bRel} (moved (list 'not (list 'genl low_a mid_a)))))))))

(defn- narrowings
  "How many `genl` edges `f` narrows, counted on `inherit/crossings`."
  [f]
  (let [n    (atom 0)
        orig @#'inherit/crossings]
    (with-redefs [inherit/crossings (fn [& args] (swap! n inc) (apply orig args))]
      (f))
    @n))

(tu/deftest-kb an-edge-is-narrowed-only-where-the-answer-is-read
  (let [{:syms [aRel low_a mid_a high_a far_u far_v]}
        (terms '[aRel low_a mid_a high_a far_u far_v])]
    (chain! kb aRel low_a mid_a high_a)
    (v/assert kb (list 'genl far_u 'thing) 'CxUniverse)
    (v/assert kb (list 'genl far_v 'thing) 'CxUniverse)
    (testing "the re-join reads rules, and no predicate the edge moves carries one"
      (is (zero? (narrowings #(inherit/rejoin-rules kb (list 'genl far_u far_v))))))
    (testing "recover's settle holds every stored sentex, and so every extent a moved
              predicate would add, and narrows no edge"
      (is (zero? (narrowings #(v/recover kb)))))
    (v/assert kb (list 'set/forwardRule (list 'implies (list aRel '?x '?y) (list 'aNoted '?x '?y)))
              'CxUniverse)
    (testing "a rule on a predicate the edge would move is what the narrowing is for"
      (is (pos? (narrowings #(inherit/rejoin-rules kb (list 'genl far_u far_v)))))
      (is (nil? (inherit/rejoin-rules kb (list 'genl far_u far_v)))))))

(defn- marked-claim
  "A claim two edges above the conclusion's term that the goal reads only through a
  permuting mark, with the mark among the arriving sentences.  The claim's value sorts
  before its type (`a_val_t`, `z_top_t`), so the canonical spelling holds the type at
  the unpreserved position 2 whenever the mark is stored."
  [variant]
  (let [{:syms [low_t mid_t z_top_t a_val_t k_t rel subRel noted]}
        (terms '[low_t mid_t z_top_t a_val_t k_t rel subRel noted])
        ternary? (= variant :in-args)
        claim-on (if (= variant :sub) subRel rel)]
    {:base  (cond-> [[(list 'transitiveInArg rel 1 'genl) 'CxUniverse]
                     [(list 'set/forwardRule
                            (if ternary?
                              (list 'implies (list rel '?x '?y '?z) (list noted '?x '?y '?z))
                              (list 'implies (list rel '?x '?y) (list noted '?x '?y))))
                      'CxUniverse]]
              (= variant :sub) (conj [(list 'genl subRel rel) 'CxUniverse]))
     :rest  [[(case variant
                :in-args (list 'commutativeInArgs rel 1 2)
                (list 'commutative claim-on))
              'CxUniverse]
             [(list 'genl low_t mid_t) 'CxUniverse]
             [(list 'genl mid_t z_top_t) 'CxUniverse]
             [(if ternary? (list claim-on a_val_t z_top_t k_t) (list claim-on a_val_t z_top_t))
              'CxUniverse]]
     :goals (if ternary?
              [(list noted low_t a_val_t k_t) (list noted mid_t a_val_t k_t)]
              [(list noted low_t a_val_t) (list noted mid_t a_val_t)])}))

(defn- inverse-claim
  "A claim two edges below the conclusion's term under `transitiveInArgInverse`."
  []
  (let [{:syms [low_t mid_t top_t val_t rel noted]}
        (terms '[low_t mid_t top_t val_t rel noted])]
    {:base  [[(list 'transitiveInArgInverse rel 1 'genl) 'CxUniverse]
             [(list 'set/forwardRule (list 'implies (list rel '?x '?y) (list noted '?x '?y)))
              'CxUniverse]]
     :rest  [[(list 'genl low_t mid_t) 'CxUniverse]
             [(list 'genl mid_t top_t) 'CxUniverse]
             [(list rel low_t val_t) 'CxUniverse]]
     :goals [(list noted mid_t val_t) (list noted top_t val_t)]}))

(defn- holds-in-every-order-of [label l]
  (doseq [order (permutations (:rest l))]
    (is (every? true? (reading l order))
        (str label " " (pr-str (mapv first order))))))

(deftest a-commutative-claim-fires-whichever-sentence-arrives-last
  (holds-in-every-order-of :commutative (marked-claim :commutative)))

(deftest a-commutative-sub-predicate-claim-fires-whichever-sentence-arrives-last
  (holds-in-every-order-of :sub (marked-claim :sub)))

(deftest a-commutative-in-args-claim-fires-whichever-sentence-arrives-last
  (holds-in-every-order-of :in-args (marked-claim :in-args)))

(deftest an-inverse-claim-fires-whichever-sentence-arrives-last
  (holds-in-every-order-of :inverse (inverse-claim)))

(deftest an-unnarrowed-edge-still-fires-whichever-edge-arrives-last
  ;; the cap at zero takes every edge down the fallback
  (with-redefs [inherit/crossing-closure-cap 0]
    (holds-in-every-order :direct)))
