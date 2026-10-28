;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-test
  "Non-atomic terms (NATs) — docs/nat.md."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- k-of
  "The reified constant a stored NAT-bearing sentence's arg1 became."
  [kb h] (second (:sentence (v/sentex kb h))))

(defn- fresh-constant
  "A reified constant named by gensym rather than by content, `nat/g…`: a second
  constant for one expression, as an import can store."
  [] (symbol nat-read/nat-namespace (name (gensym "g"))))

;; ---- 1. round-trip -------------------------------------------------------

(tu/deftest-kb round-trip-stores-an-opaque-constant
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (testing "the stored sentence holds an opaque constant, not the compound"
        (is (nat-read/reified-nat-symbol? k))
        (is (= (list 'color k 'Red) (:sentence (v/sentex kb h))))
        (is (not-any? sequential? (rest (:sentence (v/sentex kb h))))))
      (testing "the materialized result type holds"
        (is (seq (v/sentexes-matching kb (list fruit k) '?ctx))))
      (testing "a NAT-bearing query resolves to the stored constant"
        (is (= [{'?c 'Red}] (v/ask kb (list 'color (list FruitFn AppleTree) '?c) 'CxUniverse))))
      (testing "display expands the constant back to its functional expression"
        (is (= (list 'color (list FruitFn AppleTree) 'Red)
               (nat/expand-expression kb (:sentence (v/sentex kb h)))))
        (let [plain (list 'color 'Apple 'Red)]
          (is (identical? plain (nat/expand-expression kb plain))
              "and returns a form holding no reified constant as the same object")))
      (testing "an unknown NAT resolves to no-match and mints nothing"
        (let [before (count (v/sentexes-matching kb (list 'natFormula '?k '?e) 'CxUniverse))]
          (is (empty? (v/sentexes-matching kb (list 'color (list FruitFn 'PearTree) '?c) '?ctx)))
          (is (= before (count (v/sentexes-matching kb (list 'natFormula '?k '?e) 'CxUniverse)))))))))

(tu/deftest-kb a-reified-constant-is-held-to-no-length-by-its-spelling
  ;; a minted name (`nat/a0IQ…`) reads as camelCase, and the mint of a function whose
  ;; result is `unary_predicate` asserts `(unary_predicate nat/K)` under `:naming :strict`
  (tu/with-terms [PropertyFn Tom Red Green Pink likesProperty]
    (doseq [s [(list 'reifiable_function PropertyFn) (list 'unary_function PropertyFn)
               (list 'result PropertyFn 'unary_predicate)]]
      (v/assert kb s 'CxUniverse {:strength :monotonic}))
    (let [k (symbol nat-read/nat-namespace (str (gensym "aTmp")))]
      (doseq [s [(list likesProperty Tom (list PropertyFn Red))
                 (list 'unary_predicate (list PropertyFn Green))
                 (list 'arity (list PropertyFn Pink) 1)
                 (list 'unary_predicate k)
                 (list k Tom)]]
        (testing (pr-str s)
          (is (integer? (v/assert kb s 'CxUniverse)))
          (is (some? (v/handle-of kb s 'CxUniverse))))))))

(tu/deftest-kb handle-of-and-why-not-resolve-a-nat-to-its-stored-constant
  ;; `ist` stores the constant, so `handle-of` resolves the compound to it, and
  ;; `(retract! kb (handle-of kb s c))` retracts the stored sentex
  (tu/with-terms [FruitFn AppleTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [s (list 'color (list FruitFn AppleTree) 'Red)
          h (v/ist kb 'CxUniverse s)]
      (testing "handle-of answers the handle ist stored, asked with the compound"
        (is (= h (v/handle-of kb s 'CxUniverse))))
      (testing "why-not of the same spelling reads the stored sentex, not :not-stored"
        (is (true? (:believed? (v/why-not kb s 'CxUniverse)))))
      (testing "an unknown NAT still answers nil and mints nothing"
        (let [before (v/sentex-count kb)]
          (is (nil? (v/handle-of kb (list 'color (list FruitFn 'PearTree) 'Red) 'CxUniverse)))
          (is (= before (v/sentex-count kb)))))
      (testing "so the documented composition retracts it"
        (is (pos? (:removed-sentexes (v/retract! kb (v/handle-of kb s 'CxUniverse)))))
        (is (nil? (v/handle-of kb s 'CxUniverse)))))))

(tu/deftest-kb assert-inert-resolves-a-known-nat-and-refuses-an-unminted-one
  ;; `assert-inert` reifies for read, never minting (docs/nat.md, Read path)
  (tu/with-terms [FruitFn AppleTree PearTree Rex]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (testing "a NAT this KB never minted is refused, storing nothing"
      (let [before (v/sentex-count kb)
            e (is (thrown? clojure.lang.ExceptionInfo
                           (v/assert-inert kb (list 'likes Rex (list FruitFn PearTree)) 'CxUniverse)))]
        (is (= :unminted-nat (:type (ex-data e))))
        (is (= before (v/sentex-count kb)))))
    (testing "a NAT minted by a prior assert stores inert under its constant"
      (let [k  (k-of kb (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse))
            hi (v/assert-inert kb (list 'likes Rex (list FruitFn AppleTree)) 'CxUniverse)]
        (is (= (list 'likes Rex k) (:sentence (v/sentex kb hi)))
            "the compound was resolved to the constant, not stored raw")
        (is (not (v/in? kb hi)) "inert means never a premise")
        (testing "handle-of of the compound spelling finds that one handle"
          (is (= hi (v/handle-of kb (list 'likes Rex (list FruitFn AppleTree)) 'CxUniverse))))
        (testing "a later assert of the same compound resolves to it — one record, then believed"
          (is (= hi (v/assert kb (list 'likes Rex (list FruitFn AppleTree)) 'CxUniverse)))
          (is (= 1 (v/count-with-functor kb 'likes)))
          (is (seq (v/sentexes-matching kb (list 'likes Rex (list FruitFn AppleTree)) 'CxUniverse))
              "premised, sentexes-matching now reifies the goal and finds it"))))))

(tu/deftest-kb canonical-sentex-resolves-a-nat-to-the-key-assert-stored
  (tu/with-terms [FruitFn AppleTree PearTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (testing "an unminted NAT keeps its compound form"
      (is (= (list 'color (list FruitFn PearTree) 'Red)
             (:sentence (v/canonical-sentex kb (list 'color (list FruitFn PearTree) 'Red)
                                            'CxUniverse)))))
    (testing "a minted NAT resolves to the constant assert stored and handle-of finds"
      (let [h      (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
            stored (:sentence (v/sentex kb h))
            canon  (:sentence (v/canonical-sentex kb (list 'color (list FruitFn AppleTree) 'Red)
                                                  'CxUniverse))]
        (is (= stored canon) "canonical-sentex agrees with the stored key")
        (is (= h (v/handle-of kb canon 'CxUniverse)) "and with handle-of")))))

;; ---- 2. dedup ------------------------------------------------------------

(tu/deftest-kb the-same-nat-yields-the-same-constant
  (tu/with-terms [FruitFn AppleTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h1 (v/assert kb (list 'color (list FruitFn AppleTree) 'Red)   'CxUniverse)
          h2 (v/assert kb (list 'taste (list FruitFn AppleTree) 'Sweet) 'CxUniverse)]
      (is (= (k-of kb h1) (k-of kb h2)))
      (testing "one natFormula maps the expression"
        (is (= 1 (count (v/sentexes-matching kb (list 'natFormula '?k (list FruitFn AppleTree))
                                             'CxUniverse))))))))

(tu/deftest-kb the-same-nat-yields-the-same-constant-in-independent-kbs
  ;; two KBs on their own memory stores stand in for two processes; the process-wide
  ;; symbol pool interns identity, never equality, so `=` is what holds across processes
  (tu/with-terms [FruitFn AppleTree]
    (let [mint! (fn [k]
                  (v/assert k (list 'reifiable_function FruitFn) 'CxUniverse)
                  (k-of k (v/assert k (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)))
          open! #(v/open-kb {:backend :memory :space (gensym "nat-determinism")})
          a     (open!)
          b     (open!)
          [k1 k2] (try [(mint! a) (mint! b)]
                       (finally (v/close! a) (v/close! b)))]
      (is (nat-read/reified-nat-symbol? k1) "a nat/ constant, not the raw compound")
      (is (= k1 k2)
          "the same expression, the same content-named constant, in two independent KBs"))))

(tu/deftest-kb a-vector-spelled-nat-is-the-nat-the-list-spelling-names
  ;; reification runs before `canon`, which makes `[F a]` and `(F a)` one sentence
  (doseq [vector-first? [false true]]
    (tu/with-terms [MotherFn Ann Tom likes]
      (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
      (let [E         (list MotherFn Ann)
            spellings [(list likes Tom E) (list likes Tom [MotherFn Ann])]
            [a b]     (if vector-first? (reverse spellings) spellings)
            ha        (v/assert kb a 'CxUniverse)
            hb        (v/assert kb b 'CxUniverse)
            what      (str (if vector-first? "vector" "list") " spelling first")]
        (is (= ha hb) (str what ": one handle for one canonical sentence"))
        (is (nat-read/reified-nat-symbol? (nth (:sentence (v/sentex kb ha)) 2))
            (str what ": and it holds the constant rather than the compound"))
        (is (= 1 (count (v/sentexes-matching kb (list 'natFormula '?k E) 'CxUniverse)))
            (str what ": one map for one expression"))))))

;; ---- 3. nested -----------------------------------------------------------

(tu/deftest-kb a-nested-nat-reifies-inner-then-outer
  (tu/with-terms [FruitFn BestTreeIn Orchard1]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'reifiable_function BestTreeIn) 'CxUniverse)
    (let [h        (v/assert kb (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
                             'CxUniverse)
          inner-k  (nat-read/dedup-constant kb (list BestTreeIn Orchard1))
          outer-k  (k-of kb h)]
      (testing "both the inner and outer NAT have a natFormula"
        (is (nat-read/reified-nat-symbol? inner-k))
        (is (nat-read/reified-nat-symbol? outer-k))
        (is (= (list FruitFn inner-k) (nat/nat-expression kb outer-k)))
        (is (= (list BestTreeIn Orchard1) (nat/nat-expression kb inner-k))))
      (testing "display expands both levels"
        (is (= (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
               (nat/expand-expression kb (:sentence (v/sentex kb h)))))))))

;; ---- 4. rename -----------------------------------------------------------

(tu/deftest-kb rename-rewrites-the-expression-keeping-the-constant-stable
  (tu/with-terms [FruitFn AppleTree MalusTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (v/assert kb (list 'rewriteOf MalusTree AppleTree) 'CxUniverse)   ; rename AppleTree -> MalusTree
      (testing "the constant is stable and its expression is rewritten"
        (is (= (list FruitFn MalusTree) (nat/nat-expression kb k)))
        (is (= k (nat-read/dedup-constant kb (list FruitFn MalusTree))))
        (is (= 1 (count (v/sentexes-matching kb (list 'natFormula '?k (list FruitFn MalusTree))
                                             'CxUniverse)))))
      (testing "the retired spelling stays a usable question, resolving to the same K"
        (is (= k (nat-read/dedup-constant kb (list FruitFn AppleTree))))))))

(tu/deftest-kb rename-collision-merges-the-two-constants
  (tu/with-terms [FruitFn AppleTree MalusTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [ha (v/assert kb (list 'color (list FruitFn AppleTree) 'Red)   'CxUniverse)
          hm (v/assert kb (list 'taste (list FruitFn MalusTree) 'Sweet) 'CxUniverse)]
      (is (not= (k-of kb ha) (k-of kb hm)))
      (let [survivor (first (sort [(k-of kb ha) (k-of kb hm)]))]
        (v/assert kb (list 'rewriteOf MalusTree AppleTree) 'CxUniverse)
        (testing "the colliding constants merge to one"
          (is (empty? (nat/colliding-constant-groups kb)))
          (is (= 1 (count (v/sentexes-matching kb (list 'natFormula '?k (list FruitFn MalusTree))
                                               'CxUniverse))))
          (is (= survivor (nat-read/dedup-constant kb (list FruitFn MalusTree)))
              "the lexicographically smallest constant survives"))))))

(tu/deftest-kb a-collision-resolves-to-the-constant-the-repair-would-keep
  ;; an import can store two constants for one expression, which no equality repairs;
  ;; the read answers with the survivor a merge would keep, in both arrival orders
  (doseq [smallest-first? [true false]]
    (tu/with-terms [FruitFn AppleTree]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (let [E     (list FruitFn AppleTree)
            ks    (vec (sort [(fresh-constant) (fresh-constant)]))
            what  (str "the " (if smallest-first? "smallest" "largest") " asserted first")]
        (doseq [k (if smallest-first? ks (rseq ks))]
          (v/assert kb (list 'natFormula k E) 'CxUniverse {:strength :monotonic}))
        (is (= 2 (count (v/sentexes-matching kb (list 'natFormula '?k E) 'CxUniverse)))
            (str what ": both maps stand, so there is a collision to resolve"))
        (is (= (first ks) (nat-read/dedup-constant kb E)) what)
        (is (= [(first ks)]
               (vec (keep (fn [[survivor dups]]
                            (when (= (set ks) (set (cons survivor dups))) survivor))
                          (nat/colliding-constant-groups kb))))
            (str what ": and the read named the survivor the repair elects"))))))

(tu/deftest-kb one-constant-mapped-to-two-expressions-is-swept-against-one-of-them
  ;; one constant mapped to two expressions: `orphan?` and `bookkeeping-handles` read the
  ;; same one.  The materialized type belongs once to the content-least expression's
  ;; function and once to the other's, which is what makes the two verdicts differ.
  (doseq [type-of-least? [true false]]
    (tu/with-terms [FruitFn SeedFn AppleTree fruit seed]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (v/assert kb (list 'reifiable_function SeedFn) 'CxUniverse)
      (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
      (v/assert kb (list 'result SeedFn seed) 'CxUniverse)
      (let [Es      (nm/sort-by-content-key identity
                                            [(list FruitFn AppleTree) (list SeedFn AppleTree)])
            least   (first Es)
            ;; the result type the mint would have written for one expression or the other
            typ     (fn [E] (if (= FruitFn (first E)) fruit seed))
            ;; one arm per arrival order of the two maps, each read back the same way
            reading (fn [order]
                      (let [k (fresh-constant)]
                        (doseq [E order]
                          (v/assert kb (list 'natFormula k E) 'CxUniverse {:strength :monotonic}))
                        (v/assert kb (list (typ (if type-of-least? least (second Es))) k)
                                  'CxUniverse {:strength :monotonic})
                        (let [stored (set (map :id (kb/find-sentexes kb k)))]
                          {:expression (nat/nat-expression kb k)
                           :orphan?    (nat/orphan? kb k)
                           :retracts   (count (nat/bookkeeping-handles kb k))
                           :stored     (count stored)
                           ;; the contract the two readers exist to keep together
                           :coherent?  (or (not (nat/orphan? kb k))
                                           (= stored (set (nat/bookkeeping-handles kb k))))})))
            fwd     (reading Es)
            rev     (reading (reverse Es))
            what    (str "the result type belongs to the " (if type-of-least? "least" "other")
                         " expression")]
        (is (= 3 (:stored fwd) (:stored rev))
            (str what ": two maps and one materialized type name the constant"))
        (is (= least (:expression fwd) (:expression rev))
            (str what ": the content-least expression answers, in either arrival order"))
        (is (:coherent? fwd) (str what ": an orphan's whole record set is what the sweep retracts"))
        (is (:coherent? rev) (str what ": and in the other arrival order too"))
        (is (= (dissoc fwd :expression) (dissoc rev :expression))
            (str what ": the sweep outcome does not depend on which map arrived first"))))))

;; ---- 5. remove -----------------------------------------------------------

(tu/deftest-kb removing-the-last-use-collects-the-orphaned-reified-nat
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (is (some? (nat/nat-expression kb k)))
      (v/retract! kb h)
      (testing "the reified NAT constant and its bookkeeping are gone, no dangling nat/ symbol"
        (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb removing-the-last-rule-naming-a-reified-nat-collects-it
  (tu/with-terms [FruitFn AppleTree fruit likes knows]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'implies (list likes '?x (list FruitFn AppleTree))
                               (list knows '?x AppleTree))
                      'CxUniverse)]
      (is (some? (nat-read/dedup-constant kb (list FruitFn AppleTree)))
          "the rule's antecedent reified the NAT")
      (v/retract! kb h)
      (testing "the teardown reads a rule's antecedent as a use, so the constant goes with it"
        (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

;; The sweep separates a use from bookkeeping by what the mint wrote, not by shape.

(tu/deftest-kb a-users-unary-claim-about-a-reified-nat-is-a-use-not-bookkeeping
  (tu/with-terms [FruitFn AppleTree prime noted Author]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h  (v/assert kb (list noted Author (list FruitFn AppleTree)) 'CxUniverse)
          k  (nth (:sentence (v/sentex kb h)) 2)
          hu (v/assert kb (list prime (list FruitFn AppleTree)) 'CxUniverse)]
      (testing "both facts stand on one constant, and neither is a declared result type"
        (is (nat-read/reified-nat-symbol? k))
        (is (= (list prime k) (:sentence (v/sentex kb hu))))
        (is (false? (nat/orphan? kb k))))
      (v/retract! kb h)
      (testing "the binary use goes and the unary claim survives, holding the constant"
        (is (seq (v/sentexes-matching kb (list prime k) 'CxUniverse)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (false? (nat/orphan? kb k))))
      (v/retract! kb hu)
      (testing "and once the claim is withdrawn the constant is collected after all"
        (is (empty? (kb/find-sentexes kb k)))
        (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

;; A use is counted by storage; the two tests below are the two ways a stored use is not a
;; believed one.

(tu/deftest-kb a-defeated-use-keeps-the-constant-until-it-is-actually-removed
  ;; the claim is defeated by the constant's own `:monotonic` materialized result type,
  ;; and retracting the separation revives it
  (tu/with-terms [FruitFn AppleTree fruit_t stone_t color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit_t) 'CxUniverse)
    (let [h (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      ;; the claim first, the separation over it after — the retroactive case, and the
      ;; policy under which a definitional clash is arbitrated rather than refused
      (let [hs (v/assert kb (list stone_t k) 'CxUniverse)
            hd (v/assert kb (list 'disjoint fruit_t stone_t) 'CxUniverse
                         {:strength :monotonic})]
        (testing "the claim is stored and OUT, outranked by the declared result type"
          (is (false? (v/in? kb hs)))
          (is (true? (v/in? kb (v/handle-of kb (list fruit_t k) 'CxUniverse)))))
        (v/retract! kb h)
        (testing "so the sweep that the last *believed* use leaving triggers keeps it"
          (is (false? (nat/orphan? kb k)))
          (is (= k (nat-read/dedup-constant kb (list FruitFn AppleTree))))
          (is (= hs (v/handle-of kb (list stone_t k) 'CxUniverse))))
        (v/retract! kb hd)
        (testing "and the defeat lifting revives a use naming a constant still mapped"
          (is (true? (v/in? kb hs)))
          (is (= (list FruitFn AppleTree) (nat/nat-expression kb k))))
        (v/retract! kb hs)
        (testing "removing it is what makes the constant an orphan, and it is collected"
          (is (empty? (kb/find-sentexes kb k)))
          (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
          (is (empty? (nat/orphaned-constants kb))))))))

(tu/deftest-kb an-inert-use-keeps-the-constant-though-it-has-no-node-at-all
  ;; an inert sentex is never a premise, so it has no TMS node to be IN or OUT
  (tu/with-terms [FruitFn AppleTree noted Author color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)
          i (v/assert-inert kb (list noted Author k) 'CxUniverse)]
      (is (nat-read/reified-nat-symbol? k))
      (is (false? (v/in? kb i)) "inert: stored, and never believed")
      (v/retract! kb h)
      (testing "the believed use went and the inert one holds the constant"
        (is (false? (nat/orphan? kb k)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (= k (nat-read/dedup-constant kb (list FruitFn AppleTree)))))
      (v/retract! kb i)
      (testing "and once that goes too the sweep collects — no dangling nat/ symbol"
        (is (empty? (kb/find-sentexes kb k)))
        (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb the-declaration-is-what-separates-a-materialized-type-from-a-claim
  (tu/with-terms [FruitFn AppleTree fruit ripe color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h  (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k  (k-of kb h)
          hr (v/assert kb (list ripe k) 'CxUniverse)]
      (testing "two unary sentexes of one shape stand on the constant"
        (is (seq (v/sentexes-matching kb (list fruit k) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list ripe k) 'CxUniverse))))
      (v/retract! kb h)
      (testing "the undeclared one is a use, so the constant outlives its other use"
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (seq (v/sentexes-matching kb (list ripe k) 'CxUniverse))))
      (v/retract! kb hr)
      (testing "the declared one is collected with the constant — no dangling nat/ symbol"
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (v/sentexes-matching kb (list fruit k) 'CxUniverse)))
        (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb a-result-declared-after-the-mint-materializes-on-the-constant
  (tu/with-terms [FruitFn AppleTree fruit color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list fruit k) 'CxUniverse))
          "the constant holds the type a mint after the declaration writes")
      (v/retract! kb h)
      (is (empty? (kb/find-sentexes kb k)) "and the type is bookkeeping, collected with it"))))

(tu/deftest-kb a-type-whose-result-declaration-was-retracted-keeps-the-constant
  (tu/with-terms [FruitFn AppleTree fruit color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [d (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
          h (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (v/retract! kb d)
      (v/retract! kb h)
      (testing "a materialized type no declaration supports is held as a use"
        (is (seq (v/sentexes-matching kb (list fruit k) 'CxUniverse)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k))))
      (v/retract! kb (v/handle-of kb (list fruit k) 'CxUniverse))
      (is (empty? (kb/find-sentexes kb k)) "and withdrawing it collects the constant"))))

(tu/deftest-kb the-bookkeeping-set-is-an-answer-rather-than-a-plan
  ;; a lazy answer fails only in some term-index orders, so the property is asserted
  ;; directly (docs/nat.md, Rename and remove)
  (tu/with-terms [FruitFn AppleTree fruit color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h  (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k  (k-of kb h)
          hs (nat/bookkeeping-handles kb k)]
      ;; the claim is that nothing in the answer is still pending, not that it is a
      ;; vector — `counted?` covers the collection this returns, `realized?` a seq some
      ;; other realization produced, and a lazy tail satisfies neither
      (is (or (counted? hs) (realized? hs))
          "realized before it is returned, not as the caller consumes it")
      (is (= 2 (count hs)) "the map and the one materialized result type"))))

;; A nested NAT whose only reference is the outer constant's map is a candidate only on
;; the round after the outer one goes.

(tu/deftest-kb collecting-an-orphan-cascades-to-the-nat-nested-in-its-expression
  (tu/with-terms [FruitFn BestTreeIn Orchard1]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'reifiable_function BestTreeIn) 'CxUniverse)
    (let [h       (v/assert kb (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
                            'CxUniverse)
          outer-k (k-of kb h)
          inner-k (nat-read/dedup-constant kb (list BestTreeIn Orchard1))]
      (testing "the inner constant is referenced only by the outer one's expression"
        (is (nat-read/reified-nat-symbol? inner-k))
        (is (= (list FruitFn inner-k) (nat/nat-expression kb outer-k)))
        (is (false? (nat/orphan? kb inner-k))))
      (v/retract! kb h)
      (testing "the outer constant goes with its last use"
        (is (empty? (kb/find-sentexes kb outer-k)))
        (is (nil? (nat-read/dedup-constant kb (list FruitFn inner-k)))))
      (testing "and the inner one goes with the expression that was naming it"
        (is (empty? (kb/find-sentexes kb inner-k)))
        (is (nil? (nat-read/dedup-constant kb (list BestTreeIn Orchard1)))))
      (is (empty? (nat/orphaned-constants kb))))))

;; Nothing is retracted here: a closed-extent negative antecedent stops holding, and the
;; settle deletes the conclusion it solely supported (docs/exceptions.md).

(tu/deftest-kb a-nat-whose-use-the-settle-swept-is-collected-too
  (tu/with-terms [FruitFn AppleTree fruity brightAs weather overcast Sunny Sun]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    ;; `fruity` is the declared result type, so the minting sentence is bookkeeping and
    ;; the rule's conclusion is the only use of the constant
    (v/assert kb (list 'result FruitFn fruity) 'CxUniverse)
    (let [h (v/assert kb (list fruity (list FruitFn AppleTree)) 'CxUniverse)
          k (k-of kb h)]
      (v/assert kb (list weather Sunny) 'CxUniverse)
      (v/assert kb (list 'closed_extent_predicate overcast) 'CxUniverse)
      (v/assert kb (list 'implies (list 'and (list fruity '?x) (list weather '?w)
                                        (list 'not (list overcast '?w)))
                         (list brightAs '?x Sun))
                'CxUniverse {:direction :forward})
      (testing "the rule's conclusion is the constant's one live use"
        (is (nat-read/reified-nat-symbol? k))
        (is (seq (v/sentexes-matching kb (list brightAs k Sun) 'CxUniverse)))
        (is (false? (nat/orphan? kb k))))
      (v/edit! kb {:add [[(list overcast Sunny) 'CxUniverse]]})
      (testing "the closed extent blocks the rule and the settle sweeps the conclusion"
        (is (empty? (v/sentexes-matching kb (list brightAs k Sun) 'CxUniverse))))
      (testing "and the constant it was the last use of goes with it"
        (is (nil? (nat/nat-expression kb k)))
        (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

;; ---- 6. unreifiable functions --------------------------------------------

(tu/deftest-kb an-unreifiable-nat-stays-structural
  (tu/with-terms [QuantityFn Obj]
    (v/assert kb (list 'unreifiable_function QuantityFn) 'CxUniverse)
    (let [nut (list QuantityFn 5 'Kilogram)
          h   (v/assert kb (list 'mass Obj nut) 'CxUniverse)]
      (testing "the compound is stored structurally, not minted"
        (is (= (list 'mass Obj nut) (:sentence (v/sentex kb h))))
        (is (nil? (nat-read/dedup-constant kb nut))))
      (testing "it round-trips unchanged"
        (is (seq (v/sentexes-matching kb (list 'mass Obj nut) '?ctx)))))))

;; ---- 7. no-op cost -------------------------------------------------------

(deftest with-no-reifiable-function-the-reify-pass-is-a-no-op
  ;; life.txt declares FatherFn reifiable, so the KB here is an empty one of its own.
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (tu/with-terms [FruitFn AppleTree]
      (testing "the presence check answers false and a plain compound is stored verbatim"
        (is (false? (nat-read/any-reifiable-functions? kb)))
        ;; a compound argument with no reifiable_function declared is left structural
        (let [h (v/assert kb (list 'grows (list FruitFn AppleTree) 'Spring) 'CxUniverse)]
          (is (= (list 'grows (list FruitFn AppleTree) 'Spring) (:sentence (v/sentex kb h)))))))))

;; ---- 8. every read path asks the same question ---------------------------

(tu/deftest-kb every-read-path-reifies-the-nat-in-its-goal
  (tu/with-terms [CapitalOfFn France isCapital Yes]
    (v/assert kb (list 'reifiable_function CapitalOfFn) 'CxUniverse)
    (let [h (v/assert kb (list isCapital (list CapitalOfFn France) Yes) 'CxUniverse)]
      (testing "the store holds a constant, so a goal spelled as the NAT must be reified"
        (is (nat-read/reified-nat-symbol? (second (:sentence (v/sentex kb h)))))))
    (doseq [goal [(list isCapital (list CapitalOfFn France) Yes)
                  (list isCapital (list CapitalOfFn France) '?w)]]
      (testing (str "the ground and open forms of " (pr-str goal))
        (is (= 1 (count (v/ask kb goal 'CxUniverse))))
        (is (= 1 (count (v/sentexes-matching kb goal 'CxUniverse))))
        (is (= 1 (count (v/prove kb [goal] 'CxUniverse))))
        (testing "the anytime ask is the same ask, not a differently-prepared one"
          (let [r (v/ask-within kb goal 'CxUniverse {})]
            (is (= :complete (:status r)))
            (is (= (v/ask kb goal 'CxUniverse) (:results r)))))
        (testing "and so are the two levels that claim to be the engine's dispatch"
          (is (= 1 (count (v/lookup kb 6 goal 'CxUniverse))))
          (is (= 1 (count (v/lookup kb 7 goal 'CxUniverse)))))))))

(tu/deftest-kb an-exceptWhen-query-meets-the-constant-its-fact-was-stored-under
  ;; an `exceptWhen`'s conjuncts arrive as a vector (docs/nat.md, Write path)
  (tu/with-terms [CapitalOfFn France isCapital Yes bird flies Tweety]
    (v/assert kb (list 'reifiable_function CapitalOfFn) 'CxUniverse)
    (v/assert kb (list bird Tweety) 'CxUniverse)
    (v/assert kb (list isCapital (list CapitalOfFn France) Yes) 'CxUniverse)
    (v/assert kb (list 'exceptWhen [(list isCapital (list CapitalOfFn France) Yes)]
                       (list 'set/defaultRule
                             (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x)))))
              'CxUniverse)
    (is (v/ask? kb (list isCapital (list CapitalOfFn France) Yes) 'CxUniverse)
        "the conjunct is answerable when it is asked as a goal")
    (is (empty? (v/sentexes-matching kb (list flies '?x) 'CxUniverse))
        "so forward chaining concludes nothing")
    (is (empty? (v/prove kb (list flies '?x) 'CxUniverse))
        "and the DFS proves nothing")
    (is (empty? (binding [v/*query-engine* :inference
                          v/*query-options*  {:max-depth 3}]
                  (v/prove kb (list flies '?x) 'CxUniverse)))
        "and neither does the node engine")))

;; ---- genlResult + rewriteOf-to-real-term ---------------------------------

(tu/deftest-kb result-genl-materializes-a-subtype-edge
  (tu/with-terms [SubtypeFn Base super]
    (v/assert kb (list 'reifiable_function SubtypeFn) 'CxUniverse)
    (v/assert kb (list 'genl super 'thing) 'CxUniverse)
    (v/assert kb (list 'genlResult SubtypeFn super) 'CxUniverse)
    (let [h (v/assert kb (list 'studies 'Alice (list SubtypeFn Base)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "the minted constant is a subtype of the result type"
        (is (nat-read/reified-nat-symbol? k))
        (is (v/genl? kb k super))))))

(tu/deftest-kb result-arg-types-an-application-that-is-never-minted
  (tu/with-terms [PickFn needsKind kind other Ann]
    (v/assert kb (list 'unreifiable_function PickFn) 'CxUniverse)
    (v/assert kb (list 'resultArg PickFn 1) 'CxUniverse)
    (v/assert kb (list 'genl kind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl other 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint kind other) 'CxUniverse)
    (v/assert kb (list 'arg needsKind 2 kind) 'CxUniverse)
    (is (some? (v/assert kb (list needsKind Ann (list PickFn kind)) 'CxUniverse))
        "an application naming the demanded type is admitted")
    (is (= :arg-type (:type (tu/write-conviction kb (list needsKind Ann (list PickFn other))
                                                 'CxUniverse)))
        "and one naming a type disjoint from it is held inert")))

(tu/deftest-kb a-goal-reads-the-result-type-of-an-application-that-is-never-minted
  (tu/with-terms [ClockFn SpanFn PickFn moment temporal other kind startsAt CxDecl]
    (doseq [f [ClockFn SpanFn PickFn]] (v/assert kb (list 'unreifiable_function f) 'CxUniverse))
    (v/assert kb (list 'genl temporal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl moment temporal) 'CxUniverse)
    (v/assert kb (list 'genl other 'thing) 'CxUniverse)
    (v/assert kb (list 'result ClockFn moment) 'CxUniverse)
    (v/assert kb (list 'resultArg PickFn 1) 'CxUniverse)
    (v/assert kb (list 'result SpanFn other) CxDecl)
    (let [t (list ClockFn 1)]
      (doseq [ty [moment temporal]]
        (testing (str "the declared result type and its genls answer, " ty)
          (is (v/ask? kb (list ty t) 'CxUniverse))
          (is (= 1 (count (v/prove kb [(list ty t)] 'CxUniverse))))
          (is (seq (binding [v/*query-engine* :inference v/*query-options* {:max-depth 3}]
                     (v/prove kb (list ty t) 'CxUniverse))))))
      (is (not (v/ask? kb (list other t) 'CxUniverse)) "a type the result does not reach answers nothing")
      (is (not (v/ask? kb (list moment (list ClockFn '?x)) 'CxUniverse)) "an open application answers nothing")
      (is (v/ask? kb (list kind (list PickFn kind)) 'CxUniverse) "a resultArg position types the application")
      (is (v/ask? kb (list other (list SpanFn t)) CxDecl) "the declaration's context reads it")
      (is (not (v/ask? kb (list other (list SpanFn t)) 'CxUniverse)) "a context that does not see it reads nothing")
      (testing "a backward rule's membership antecedent is discharged for the application"
        (v/assert kb (list 'set/backwardRule
                           (list 'implies (list moment '?m) (list startsAt (list SpanFn '?m) '?m)))
                  'CxUniverse)
        (let [g (list startsAt (list SpanFn t) '?w)]
          (is (= [{'?w t}] (v/prove kb [g] 'CxUniverse)))
          (is (= [{'?w t}] (distinct (binding [v/*query-engine* :inference v/*query-options* {:max-depth 3}]
                                       (v/prove kb g 'CxUniverse))))))))
    (testing "the shipped result of InstantFn answers time_point"
      (is (v/ask? kb '(time_point (InstantFn 2026 10 6 0 0 0)) 'CxUniverse)))))

(tu/deftest-kb a-result-arg-membership-entailed-off-the-map-is-bookkeeping
  (tu/with-terms [MemberFn kind studies Alice]
    (tu/with-entailing
      (v/assert kb (list 'reifiable_function MemberFn) 'CxUniverse)
      (v/assert kb (list 'resultArg MemberFn 1) 'CxUniverse)
      (let [h (v/assert kb (list studies Alice (list MemberFn kind)) 'CxUniverse)
            k (nth (:sentence (v/sentex kb h)) 2)]
        (is (v/believed? kb (v/handle-of kb (list kind k) 'CxUniverse) 'CxUniverse))
        (v/retract! kb h)
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb)))))))

(defn- believed-naming
  "The believed sentences naming any of `terms`."
  [kb terms]
  (into #{} (comp (mapcat #(kb/find-sentexes kb %)) (filter #(v/in? kb (:id %))) (map :sentence))
        terms))

(tu/deftest-kb a-membership-entailed-off-a-materialized-genl-edge-is-bookkeeping
  (doseq [order [:declared-before-the-use :declared-after-the-use]]
    (tu/with-terms [FruitFn AppleTree sub_t color]
      (tu/with-entailing
        (let [decls  [(list 'reifiable_function FruitFn) (list 'genl sub_t 'thing)]
              gr     (list 'genlResult FruitFn sub_t)
              terms  [FruitFn AppleTree sub_t color]
              _      (doseq [s decls] (v/assert kb s 'CxUniverse))
              _      (when (= order :declared-before-the-use) (v/assert kb gr 'CxUniverse))
              h      (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
              k      (k-of kb h)
              _      (when (= order :declared-after-the-use) (v/assert kb gr 'CxUniverse))]
          ;; `(predicate k)` rests on the materialized `(genl k sub_t)`, not on the map
          (is (v/believed? kb (v/handle-of kb (list 'predicate k) 'CxUniverse) 'CxUniverse)
              (str order))
          (v/retract! kb h)
          (is (empty? (kb/find-sentexes kb k)) (str order))
          (is (= (tu/with-cleared-kb [fresh #(tu/load-core! (tu/isolated-fresh))]
                   (tu/with-entailing (doseq [s (conj decls gr)] (v/assert fresh s 'CxUniverse)))
                   (believed-naming fresh terms))
                 (believed-naming kb terms))
              (str order ": belief matches a fresh load of the final state")))))))

(tu/deftest-kb rewriteof-reifies-a-nat-to-an-existing-real-term
  (tu/with-terms [CapitalFn France Paris]
    (v/assert kb (list 'reifiable_function CapitalFn) 'CxUniverse)
    ;; (CapitalFn France) should reify to the real Paris, not a fresh constant
    (v/assert kb (list 'rewriteOf Paris (list CapitalFn France)) 'CxUniverse)
    (let [h (v/assert kb (list 'locatedIn (list CapitalFn France) 'Europe) 'CxUniverse)]
      (testing "the NAT resolves to the declared real term"
        (is (= (list 'locatedIn Paris 'Europe) (:sentence (v/sentex kb h))))
        (is (= [(list 'locatedIn Paris 'Europe)]
               (map :sentence (v/sentexes-matching kb (list 'locatedIn (list CapitalFn France) '?where)
                                                   '?ctx))))))))

(tu/deftest-kb two-rewrite-declarations-mint-fresh-rather-than-electing-one
  (tu/with-terms [MotherFn Muffet Mary Maria]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf Mary (list MotherFn Muffet)) 'CxUniverse)
    (v/assert kb (list 'rewriteOf Maria (list MotherFn Muffet)) 'CxUniverse)
    (let [h      (v/assert kb (list 'likes 'Tom (list MotherFn Muffet)) 'CxUniverse)
          stored (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat-read/reified-nat-symbol? stored)
          "a fresh constant stands until the disagreement is resolved")
      (is (not (contains? #{Mary Maria} stored))))))

;; ---- recover: the reifiable presence check + reified NAT data survive a rebuild ---

(tu/deftest-kb nat-data-survives-recover
  ;; `recover` adds no sentex, so the fixture's net-neutral teardown still holds
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (v/recover kb)
      (testing "the presence check, the constant map, and the materialized type all rebuild"
        (is (true? (nat-read/any-reifiable-functions? kb)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (= k (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (seq (v/sentexes-matching kb (list fruit k) '?ctx))))
      (testing "a fresh NAT still dedups to the same constant after recovery"
        (let [h2 (v/assert kb (list 'taste (list FruitFn AppleTree) 'Sweet) 'CxUniverse)]
          (is (= k (k-of kb h2))))))))

;; ---- the corresponding predicate -----------------------------------------

(tu/deftest-kb a-corresponding-fact-names-the-term-an-application-reifies-to
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)]
      (testing "the application resolves to the value, and mints nothing beside it"
        (is (= (list caresFor Bob Mary) (:sentence (v/sentex kb h))))
        (is (empty? (v/sentexes-matching kb (list 'natFormula '?k (list MotherFn Muffet))
                                         'CxUniverse))))
      (testing "a query written with the application still finds it"
        (is (= [{'?w Bob}] (v/ask kb (list caresFor '?w (list MotherFn Muffet)) 'CxUniverse)))))))

(tu/deftest-kb an-application-with-no-value-mints-a-constant-that-answers-the-predicate
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "no value is known, so the expression mints a placeholder"
        (is (nat-read/reified-nat-symbol? k)))
      (testing "and the placeholder is projected onto the corresponding predicate"
        (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))))))

(tu/deftest-kb a-value-arriving-after-the-mint-retires-the-placeholder
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat-read/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse {:strength :monotonic})
      (testing "one value, and it is the one somebody named"
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse))))
      (testing "the use of the placeholder migrated onto it"
        (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx))))
      (testing "and the expression still resolves — to the real term now"
        (is (= Mary (nat-read/dedup-constant kb (list MotherFn Muffet))))
        (is (= Mary (nat-read/correspondence-value kb (list MotherFn Muffet) nil)))))))

(tu/deftest-kb a-declared-position-puts-the-value-where-it-says
  ;; Cyc's own example: (StreetCornerFn XING DIRECTION) = LOT exactly when
  ;; (streetCornerOf LOT XING DIRECTION), so the value is argument 1 and not the last.
  (tu/with-terms [StreetCornerFn streetCornerOf Xing1 North Lot7 ownedBy Alice]
    (v/assert kb (list 'reifiable_function StreetCornerFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate StreetCornerFn streetCornerOf 1)
              'CxUniverse)
    (v/assert kb (list streetCornerOf Lot7 Xing1 North) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list ownedBy (list StreetCornerFn Xing1 North) Alice) 'CxUniverse)]
      (is (= (list ownedBy Lot7 Alice) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-declaration-arriving-last-reconciles-what-was-already-minted
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat-read/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse {:strength :monotonic})
      (testing "before the declaration the two terms are unrelated"
        (is (= k (nat-read/dedup-constant kb (list MotherFn Muffet)))))
      (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
      (testing "declaring it last reaches the state declaring it first would have"
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx)))
        (is (= Mary (nat-read/dedup-constant kb (list MotherFn Muffet))))))))

(tu/deftest-kb a-declaration-arriving-last-projects-a-placeholder-that-has-no-value
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (empty? (v/ask kb (list motherOf Muffet '?m) '?ctx)))
      (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
      (testing "the constant minted before the declaration is projected by it"
        (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))))))

(tu/deftest-kb two-declarations-for-one-function-decide-nothing
  (tu/with-terms [MotherFn motherOf parentOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn parentOf 2) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat-read/reified-nat-symbol? k))
      (is (not= Mary k))
      (testing "and each declaration projects the placeholder onto its own predicate"
        (is (= [{'?m k}] (v/ask kb (list parentOf Muffet '?m) 'CxUniverse)))
        (is (= #{{'?m Mary} {'?m k}} (set (v/ask kb (list motherOf Muffet '?m) 'CxUniverse))))))))

(tu/deftest-kb retracting-the-declaration-stops-the-application-resolving
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor sees]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [d (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)]
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse {:strength :monotonic})
      (is (= Mary (nat-read/correspondence-value kb (list MotherFn Muffet) nil)))
      (v/retract! kb d)
      (testing "the declaration is belief-following, so the reify stops reading it"
        (is (nil? (nat-read/correspondence-value kb (list MotherFn Muffet) nil)))
        (let [h (v/assert kb (list sees Bob (list MotherFn Muffet)) 'CxUniverse)]
          (is (nat-read/reified-nat-symbol? (nth (:sentence (v/sentex kb h)) 2))))))))

;; ---- a map leaving before or without its mark ------------------------------

(defn- stored-sentences
  "Every stored sentex's sentence, believed or not: a re-spell in place keeps the handle,
  so the handle set alone misses it."
  [kb]
  (into #{} (keep #(some-> (v/sentex kb %) v/sentence-of)) (tu/sentex-ids kb)))

(tu/deftest-kb a-mark-and-its-maps-retracted-in-any-order-leave-no-constant
  (doseq [[label teardown]
          [["the mark alone"          (fn [kb mark _] (v/retract! kb mark))]
           ["every map, then the mark" (fn [kb mark maps] (run! #(v/retract! kb %) maps) (v/retract! kb mark))]
           ["one map, then the mark"  (fn [kb mark maps] (v/retract! kb (first maps)) (v/retract! kb mark))]]]
    (tu/with-terms [SkillFn Rex Ann likes]
      (let [before (stored-sentences kb)
            uses   (mapv #(v/assert kb (list likes % (list SkillFn %)) 'CxUniverse) [Rex Ann])
            mark   (v/assert kb (list 'reifiable_function SkillFn) 'CxUniverse)
            maps   (mapv (fn [x use]
                           (v/handle-of kb (list 'natFormula (nth (:sentence (v/sentex kb use)) 2) (list SkillFn x))
                                        'CxUniverse))
                         [Rex Ann] uses)]
        (is (every? some? maps) label)
        (teardown kb mark maps)
        (is (= (mapv #(list likes % (list SkillFn %)) [Rex Ann])
               (mapv #(:sentence (v/sentex kb %)) uses))
            label)
        (run! #(v/retract! kb %) uses)
        (is (= before (stored-sentences kb)) label)))))

(tu/deftest-kb a-map-retracted-under-its-believed-mark-is-minted-again
  (tu/with-terms [SkillFn Rex likes]
    (let [use  (v/assert kb (list likes Rex (list SkillFn Rex)) 'CxUniverse)
          _    (v/assert kb (list 'reifiable_function SkillFn) 'CxUniverse)
          k    (nth (:sentence (v/sentex kb use)) 2)
          map-handle (fn [] (v/handle-of kb (list 'natFormula k (list SkillFn Rex)) 'CxUniverse))]
      (is (nat-read/reified-object-symbol? k))
      (v/retract! kb (map-handle))
      (is (some? (map-handle)))
      (is (= (list likes Rex k) (:sentence (v/sentex kb use))))
      (is (v/ask? kb (list likes Rex (list SkillFn Rex)) 'CxUniverse)))))

(tu/deftest-kb an-inner-constant-whose-map-left-is-minted-again-and-expanded-with-the-marks
  ;; the inner constant's only row besides its map is the outer constant's map, a mention
  (tu/with-terms [InnerFn OuterFn Rex likes]
    (let [before  (stored-sentences kb)
          written (list likes Rex (list OuterFn (list InnerFn Rex)))
          use     (v/assert kb written 'CxUniverse)
          marks   (mapv #(v/assert kb (list 'reifiable_function %) 'CxUniverse) [InnerFn OuterFn])
          spelled (:sentence (v/sentex kb use))
          inner   (list 'natFormula (second (nat/nat-expression kb (nth spelled 2))) (list InnerFn Rex))]
      (v/retract! kb (v/handle-of kb inner 'CxUniverse))
      (is (some? (v/handle-of kb inner 'CxUniverse)))
      (is (= spelled (:sentence (v/sentex kb use))))
      (run! #(v/retract! kb %) marks)
      (is (= written (:sentence (v/sentex kb use))))
      (v/retract! kb use)
      (is (= before (stored-sentences kb))))))

(tu/deftest-kb an-ill-formed-correspondence-is-refused
  (tu/with-terms [MotherFn motherOf Mary]
    ;; the arity-1 row is caught by the NAMING entry point, which runs upstream of `wff`: a
    ;; camelCase functor at arity 1 is a unary predicate wearing a relation's spelling,
    ;; and `problems` names that before `wff` gets to count the arguments
    (doseq [[what expected s]
            [["one argument"      :naming
              (list 'functionCorrespondingPredicate MotherFn)]
             ["four arguments"    :not-well-formed
              (list 'functionCorrespondingPredicate MotherFn motherOf 2 2)]
             ["an individual"     :not-well-formed
              (list 'functionCorrespondingPredicate MotherFn Mary 2)]
             ["a position that is not a positive integer" :not-well-formed
              (list 'functionCorrespondingPredicate MotherFn motherOf 'first)]]]
      (let [e (try (v/assert kb s 'CxUniverse) nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) what)
        (is (= expected (:type (ex-data e))) what)))))

(tu/deftest-kb a-correspondence-survives-recover
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse {:strength :monotonic})
    (v/recover kb)
    (is (= Mary (nat-read/correspondence-value kb (list MotherFn Muffet) nil)))
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)]
      (is (= (list caresFor Bob Mary) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-projection-does-not-keep-an-orphaned-placeholder-alive
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (seq (v/ask kb (list motherOf Muffet '?m) '?ctx)))
      (v/retract! kb h)
      (testing "the placeholder, its map and its projection all go"
        (is (nil? (nat-read/dedup-constant kb (list MotherFn Muffet))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (v/ask kb (list motherOf Muffet '?m) '?ctx)))
        (is (empty? (nat/orphaned-constants kb)))))))

;; ---- the result type reaches the corresponding predicate -----------------
;; A function's result type is the type of the value its corresponding predicate holds at
;; the value position, so `result` and the correspondence together type that argument of
;; the predicate.  The vocabulary below is made up, so the tests read the rules and no
;; shipped function.

(tu/deftest-kb a-correspondence-types-the-value-argument-of-its-predicate-by-the-result
  ;; [function metatype, predicate metatype, predicate arity, declared position]
  (doseq [[fn-type pred-type arity value]
          [['unary_function      'binary_predicate     2 2]
           ['binary_function     'ternary_predicate    3 3]
           ['ternary_function    'quaternary_predicate 4 4]
           ['quaternary_function 'quinary_predicate    5 5]
           ['binary_function     'ternary_predicate    3 1]]]
    (tu/with-terms [ShadeFn shadeOf paint shade]
      (let [other (if (= value arity) (dec arity) arity)
            what  (str pred-type " valued at " value)]
        (v/assert kb (list 'reifiable_function ShadeFn) 'CxUniverse)
        (v/assert kb (list fn-type ShadeFn) 'CxUniverse)
        (v/assert kb (list pred-type shadeOf) 'CxUniverse)
        (doseq [position (range 1 (inc arity)) :when (not= position value)]
          (v/assert kb (list 'arg shadeOf position paint) 'CxUniverse))
        (v/assert kb (list 'result ShadeFn shade) 'CxUniverse)
        (v/assert kb (list 'functionCorrespondingPredicate ShadeFn shadeOf value) 'CxUniverse)
        (is (true? (v/ask? kb (list 'arg shadeOf value shade) 'CxUniverse)) what)
        (is (false? (v/ask? kb (list 'arg shadeOf other shade) 'CxUniverse))
            (str what ": and no other position"))))))

;; ---- the derivation path -------------------------------------------------
;; A forward rule whose consequent names an application concludes about the value its
;; corresponding predicate names, which is the constant `assert` minted for it, and mints
;; nothing itself.  A derived sentence and an asserted one about the same application
;; meet in a join, answer a goal spelled with the compound, and carry the result type.

(defn- orchard-rules!
  "The correspondence of `FruitFn`, the rule that concludes about an application, and the
  rule that joins it with an asserted claim about the same application."
  [kb FruitFn fruitOf bears grownIn tagged picked]
  (v/assert kb (list 'functionCorrespondingPredicate FruitFn fruitOf 2) 'CxUniverse)
  (v/assert kb (list 'set/forwardRule
                     (list 'implies (list bears '?t '?o) (list grownIn (list FruitFn '?t) '?o)))
            'CxUniverse)
  (v/assert kb (list 'set/forwardRule
                     (list 'implies (list 'and (list tagged '?f) (list grownIn '?f '?o))
                           (list picked '?o)))
            'CxUniverse))

(defn- derived-and-asserted-name-one-constant
  "Build the orchard in `order` — `:derived-first` stores the rules and the fact the
  application is derived from before the claim that spells it, `:asserted-first` the
  claim first — and check the two uses name one constant."
  [kb order]
  (tu/with-terms [FruitFn AppleTree Orchard fruit fruitOf bears grownIn tagged picked]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [derive! #(do (orchard-rules! kb FruitFn fruitOf bears grownIn tagged picked)
                       (v/assert kb (list bears AppleTree Orchard) 'CxUniverse))
          claim!  #(v/assert kb (list tagged (list FruitFn AppleTree)) 'CxUniverse)
          _       (if (= order :derived-first) (do (derive!) (claim!)) (do (claim!) (derive!)))
          k       (nat-read/dedup-constant kb (list FruitFn AppleTree))]
      (testing (str order ": the derived sentence holds the constant, not the compound")
        (is (nat-read/reified-nat-symbol? k))
        (is (= [(list grownIn k Orchard)]
               (map :sentence (v/sentexes-matching kb (list grownIn '?f Orchard) 'CxUniverse))))
        (is (= [(list tagged k)]
               (map :sentence (v/sentexes-matching kb (list tagged '?f) 'CxUniverse)))))
      (testing (str order ": a goal spelled with the compound finds the derived fact")
        (is (v/ask? kb (list grownIn (list FruitFn AppleTree) Orchard) 'CxUniverse))
        (is (v/query? kb (list grownIn (list FruitFn AppleTree) Orchard) 'CxUniverse))
        (is (= #{'CxUniverse}
               (set (v/contexts-of kb (list grownIn (list FruitFn AppleTree) Orchard))))))
      (testing (str order ": the constant carries the function's result type")
        (is (v/ask? kb (list fruit k) 'CxUniverse)))
      (testing (str order ": a join between the asserted and the derived use meets")
        (is (= [{'?o Orchard}]
               (map #(select-keys % ['?o])
                    (v/query kb [(list tagged '?f) (list grownIn '?f '?o)] 'CxUniverse))))
        (is (v/ask? kb (list picked Orchard) 'CxUniverse)
            "the forward rule joining the two fires")))))

(tu/deftest-kb a-derived-application-names-the-constant-an-asserted-one-names
  (derived-and-asserted-name-one-constant kb :derived-first)
  (derived-and-asserted-name-one-constant kb :asserted-first))

(defn- withdrawal-collects-the-constant
  "Derive and assert one application, then retract the two uses in `order` — `:derived`
  retracts the fact the derived use rests on first, `:asserted` the claim first.  The
  constant outlives the first retraction and is collected by the second."
  [kb order]
  (tu/with-terms [FruitFn AppleTree Orchard fruit fruitOf bears grownIn tagged picked]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (orchard-rules! kb FruitFn fruitOf bears grownIn tagged picked)
    (let [hb (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)
          ht (v/assert kb (list tagged (list FruitFn AppleTree)) 'CxUniverse)
          k  (nat-read/dedup-constant kb (list FruitFn AppleTree))
          [first-h second-h] (if (= order :derived) [hb ht] [ht hb])]
      (is (nat-read/reified-nat-symbol? k))
      (v/retract! kb first-h)
      (testing (str order ": the remaining use keeps the constant")
        (is (= k (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (false? (nat/orphan? kb k)))
        (is (not (v/ask? kb (list picked Orchard) 'CxUniverse)) "the join lost one side"))
      (when (= order :derived)
        (testing "retracting the antecedent withdraws the derived fact"
          (is (empty? (v/sentexes-matching kb (list grownIn '?f Orchard) 'CxUniverse)))))
      (v/retract! kb second-h)
      (testing (str order ": the last use going collects the constant and its bookkeeping")
        (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb withdrawing-the-derived-use-collects-the-constant-in-either-order
  (withdrawal-collects-the-constant kb :derived)
  (withdrawal-collects-the-constant kb :asserted))

(tu/deftest-kb a-constant-minted-by-a-firing-is-collected-and-re-minted-under-its-name
  ;; the consequent stays as written, so the firing mints `(FruitFn AppleTree)` with no
  ;; value stored for it, and the correspondence projects the new constant
  (tu/with-terms [FruitFn AppleTree Orchard fruit fruitOf bears grownIn tagged picked]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (orchard-rules! kb FruitFn fruitOf bears grownIn tagged picked)
    (let [h (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)
          k (nat-read/dedup-constant kb (list FruitFn AppleTree))]
      (testing "the firing alone mints the constant"
        (is (nat-read/reified-nat-symbol? k))
        (is (= [(list grownIn k Orchard)]
               (mapv :sentence (v/sentexes-matching kb (list grownIn '?f Orchard) 'CxUniverse))))
        (is (v/ask? kb (list fruitOf AppleTree k) 'CxUniverse)))
      (v/retract! kb h)
      (testing "the derived use was the only one, so the constant goes with it"
        (is (nil? (nat-read/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb))))
      (let [h2 (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)]
        (testing "re-deriving mints the same constant, since the name is the expression's"
          (is (= k (nat-read/dedup-constant kb (list FruitFn AppleTree))))
          (is (v/ask? kb (list grownIn k Orchard) 'CxUniverse)))
        (v/retract! kb h2)))))

(tu/deftest-kb a-conclusion-the-checks-drop-mints-no-constant
  ;; a convicted input of a function application drops the firing's conclusion, and the
  ;; checks read the application before the mint, so the drop leaves no constant behind
  (tu/with-terms [FruitFn Orchard source grownIn]
    (doseq [s [(list 'reifiable_function FruitFn) (list 'unary_function FruitFn)
               (list 'arg FruitFn 1 'integer) (list 'result FruitFn 'thing)
               (list 'set/forwardRule
                     (list 'implies (list source '?x) (list grownIn (list FruitFn '?x) Orchard)))]]
      (v/assert kb s 'CxUniverse))
    (v/assert kb (list source "x") 'CxUniverse)
    (v/assert kb (list source 5) 'CxUniverse)
    (let [k (nat-read/dedup-constant kb (list FruitFn 5))]
      (is (= [(list grownIn k Orchard)]
             (mapv :sentence (v/sentexes-matching kb (list grownIn '?f Orchard) 'CxUniverse)))
          "only the well-typed conclusion is stored"))
    (is (nil? (nat-read/dedup-constant kb (list FruitFn "x"))) "and nothing was minted for the drop")
    (is (some #(= grownIn (first (:sentence %))) (v/violations kb))
        "the drop is recorded")))

(tu/deftest-kb a-generated-rule-names-the-constant-in-its-antecedent
  ;; a generator's generated rule is a derived conclusion too, and a ground application in
  ;; its antecedent has to be the constant the stored claim is spelled with, or the
  ;; generated rule never matches the claim
  (tu/with-terms [FruitFn AppleTree marked tagged ripe]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list tagged (list FruitFn AppleTree)) 'CxUniverse)
    (v/assert kb (list 'implies (list marked '?t)
                       (list 'set/forwardRule
                             (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t))))
              'CxUniverse)
    (v/assert kb (list marked AppleTree) 'CxUniverse)
    (is (v/ask? kb (list ripe AppleTree) 'CxUniverse))))

(tu/deftest-kb a-mint-whose-projection-fails-a-declared-type-holds-the-projection-inert
  ;; the correspondence projects the new constant onto a predicate whose `arg` declaration
  ;; its result type is disjoint from, so the mint's own assert holds the projection inert
  ;; and the fact or the firing's conclusion is stored.  Forced to the constraint reading,
  ;; where the declaration convicts the constant; the entailing one mints `(beast …)`
  ;; beside `(fruit …)` and stores the clash (docs/argtypes.md)
  (tu/without-entailing
   (tu/with-terms [FruitFn AppleTree Pear Orchard fruit beast keeperOf bears grownIn tagged]
     (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
     (v/assert kb (list 'genl fruit 'thing) 'CxUniverse)
     (v/assert kb (list 'genl beast 'thing) 'CxUniverse)
     (v/assert kb (list 'disjoint fruit beast) 'CxUniverse)
     (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
     (v/assert kb (list 'arg keeperOf 2 beast) 'CxUniverse)
     (v/assert kb (list 'functionCorrespondingPredicate FruitFn keeperOf 2) 'CxUniverse)
     (testing "the assert path stores the application and holds its projection"
       (is (some? (v/assert kb (list tagged (list FruitFn Pear)) 'CxUniverse))))
     (v/assert kb (list 'set/forwardRule
                        (list 'implies (list bears '?t '?o) (list grownIn (list FruitFn '?t) '?o)))
               'CxUniverse)
     (is (some? (v/assert kb (list bears AppleTree Orchard) 'CxUniverse))
         "the assert that fires the rule is not refused")
     (is (seq (v/sentexes-matching kb (list grownIn '?f Orchard) 'CxUniverse))
         "the conclusion is stored")
     (let [vs (v/violations kb)]
       (is (= #{[keeperOf AppleTree] [keeperOf Pear]}
              (into #{} (comp (filter #(= :inert-argument (:violation %)))
                              (map #(vec (take 2 (:sentence %)))))
                    vs))
           "both projections are held inert")
       (is (not-any? #(= :mint-refused (:violation %)) vs))))))

;; ---- an open application read through its corresponding predicate --------

(defn- orders
  "Every ordering of `xs`."
  [xs]
  (if (empty? xs)
    [[]]
    (for [x xs, more (orders (remove #{x} xs))] (cons x more))))

(defn- answers
  "`goal`'s answers in `ctx` (CxUniverse) under `engine`, projected onto `vars`, as a set."
  ([kb engine goal vars] (answers kb engine goal vars 'CxUniverse))
  ([kb engine goal vars ctx]
   (into #{} (map #(select-keys % vars))
         (binding [v/*query-engine* engine
                   v/*query-options* {:max-depth 4}]
           (v/prove kb goal ctx)))))

(defn- names?
  "Does the stored sentence of handle `h` name `term`?"
  [kb h term]
  (let [sx (v/sentex kb h)]
    (boolean (some #{term} (tree-seq sequential? seq [(:antecedent sx) (:consequent sx) (:sentence sx)])))))

(tu/deftest-kb an-open-application-reads-through-the-corresponding-predicate-in-every-order
  ;; the four pieces in all 24 orders: the reifiable mark, the correspondence, the rules
  ;; and the fact the mint names.  Every engine reads the respelled rules alike.  The
  ;; backward rule's consequent stays as written, so no goal over the application or its
  ;; constant reaches it, and an open goal binds the application as written.
  (doseq [order (orders [:mark :corr :rules :fact])]
    (tu/with-terms [FruitFn AppleTree Orchard Ann bears grownIn tagged ripe sweet fruitOf favoriteFood]
      (let [steps {:mark  [(list 'reifiable_function FruitFn)]
                   :corr  [(list 'functionCorrespondingPredicate FruitFn fruitOf 2)]
                   :rules [(list 'implies (list bears '?t '?o) (list grownIn (list FruitFn '?t) '?o))
                           (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t))
                           (list 'set/forwardRule
                                 (list 'implies (list tagged (list FruitFn '?t)) (list sweet '?t)))]
                   :fact  [(list tagged (list FruitFn AppleTree))
                           (list favoriteFood Ann (list FruitFn AppleTree))]}
            _     (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)
            hs    (into {} (map (fn [step] [step (mapv #(v/assert kb % 'CxUniverse) (steps step))])) order)
            k     (nat-read/dedup-constant kb (list FruitFn AppleTree))
            row   (fn [engine]
                    [(answers kb engine (list grownIn k '?o) ['?o])
                     (answers kb engine (list grownIn (list FruitFn AppleTree) '?o) ['?o])
                     (answers kb engine (list grownIn '?f '?o) ['?f '?o])
                     (answers kb engine [(list tagged '?f) (list grownIn '?f '?o)] ['?f '?o])
                     (answers kb engine (list ripe '?t) ['?t])
                     (answers kb engine (list grownIn (list FruitFn '?t) '?o) ['?t '?o])
                     (answers kb engine (list favoriteFood Ann (list FruitFn '?tree)) ['?tree])
                     (answers kb engine [(list 'equals '?food (list FruitFn '?tree)) (list favoriteFood Ann '?food)]
                              ['?food '?tree])])
            want  [#{} #{} #{{'?f (list FruitFn AppleTree) '?o Orchard}}
                   #{} #{{'?t AppleTree}} #{}
                   #{{'?tree AppleTree}} #{{'?food k '?tree AppleTree}}]]
        (is (nat-read/reified-nat-symbol? k) (str order))
        (is (= want (row :dfs)) (str order " dfs"))
        (is (= want (row :inference)) (str order " node engine"))
        (is (v/ask? kb (list sweet AppleTree) 'CxUniverse) (str order " forward"))
        (is (= [[true false] [false true] [false true]]
               (mapv #(vector (names? kb % FruitFn) (names? kb % fruitOf)) (:rules hs)))
            (str order " antecedents are stored respelled, the consequent as written"))))))

(tu/deftest-kb a-forward-equals-over-unminted-applications-mints-both-in-every-order
  ;; the firing mints both applications before it stores the equality, as `assert` of
  ;; the same sentence does, so the equals check reads each as the constant it becomes
  (doseq [corr? [false true]
          order (orders (cond-> [:mark :rule :fact] corr? (conj :corr)))]
    (tu/with-terms [PairFn Ann Bob Cal Dee linkedQuad pairOf CxA]
      (let [mono  {:strength :monotonic}
            steps {:mark [(list 'reifiable_function PairFn) 'CxUniverse]
                   :corr [(list 'functionCorrespondingPredicate PairFn pairOf 3) 'CxUniverse]
                   :rule [(list 'set/forwardOnlyRule
                                (list 'implies (list linkedQuad '?a '?b '?c '?d)
                                      (list 'equals (list PairFn '?a '?b) (list PairFn '?c '?d))))
                          CxA]
                   :fact [(list linkedQuad Ann Bob Cal Dee) CxA]}]
        (doseq [s [(list 'binary_function PairFn) (list 'arity linkedQuad 4)
                   (list 'forced_monotonic_predicate linkedQuad) (list 'genlCx CxA 'CxUniverse)]]
          (v/assert kb s 'CxUniverse mono))
        (doseq [step order] (let [[s cx] (steps step)] (v/assert kb s cx mono)))
        (let [k1 (nat-read/dedup-constant kb (list PairFn Ann Bob))
              k2 (nat-read/dedup-constant kb (list PairFn Cal Dee))
              at (str (vec order))]
          (is (and (nat-read/reified-nat-symbol? k1) (nat-read/reified-nat-symbol? k2) (not= k1 k2)) at)
          (is (= [(sort-by str [k1 k2])]
                 (mapv #(sort-by str (rest (:sentence %))) (v/sentexes-matching kb '(equals ?x ?y) CxA)))
              at)
          (is (= (if corr? [true true] [false false])
                 [(v/ask? kb (list pairOf Ann Bob k1) 'CxUniverse) (v/ask? kb (list pairOf Cal Dee k2) 'CxUniverse)])
              at)
          (is (not-any? #(= :not-well-formed (:violation %)) (v/violations kb)) at))))))

(tu/deftest-kb both-spellings-of-a-respelled-rule-are-one-handle
  (tu/with-terms [FruitFn tagged ripe fruitOf]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate FruitFn fruitOf 2) 'CxUniverse)
    (let [respelled (list 'implies (list 'and (list fruitOf '?t '?f) (list tagged '?f)) (list ripe '?t))
          h         (v/assert kb (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t)) 'CxUniverse)]
      (is (= h (v/assert kb respelled 'CxUniverse)))
      (is (= h (v/assert kb (list 'implies (list 'and (list 'equals '?f (list FruitFn '?t)) (list tagged '?f))
                                  (list ripe '?t))
                         'CxUniverse))
          "an equals of an application is its corresponding literal")
      (is (= (select-keys (v/canonical-sentex kb respelled 'CxUniverse) [:antecedent :consequent])
             (select-keys (v/sentex kb h) [:antecedent :consequent]))))))

(tu/deftest-kb an-open-application-goal-answers-through-a-correspondence-value-in-either-order
  ;; a value the KB states, not a minted constant: the goal reads `(fruitOf AppleTree Gala)`
  (doseq [value-first? [true false]]
    (tu/with-terms [FruitFn AppleTree Gala Ann favoriteFood fruitOf]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (v/assert kb (list 'functionCorrespondingPredicate FruitFn fruitOf 2) 'CxUniverse)
      (let [steps [(list fruitOf AppleTree Gala) (list favoriteFood Ann (list FruitFn AppleTree))]]
        (run! #(v/assert kb % 'CxUniverse {:strength :monotonic}) (cond-> steps (not value-first?) reverse)))
      (doseq [engine [:dfs :inference]]
        (is (= [#{{'?tree AppleTree}} #{{'?food Gala '?tree AppleTree}}]
               [(answers kb engine (list favoriteFood Ann (list FruitFn '?tree)) ['?tree])
                (answers kb engine [(list 'equals '?food (list FruitFn '?tree)) (list favoriteFood Ann '?food)]
                         ['?food '?tree])])
            (str value-first? " " engine))))))

(tu/deftest-kb a-rule-goes-inert-live-inert-as-its-correspondence-comes-and-goes
  (tu/with-terms [FruitFn AppleTree tagged ripe fruitOf]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list tagged (list FruitFn AppleTree)) 'CxUniverse)
    (let [h     (v/assert kb (list 'set/forwardRule
                                   (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t)))
                          'CxUniverse)
          ripe? #(v/ask? kb (list ripe AppleTree) 'CxUniverse)]
      (testing "no correspondence: the rule is held and fires nothing"
        (is (not (ripe?)))
        (is (empty? (v/prove kb (list ripe '?t) 'CxUniverse)))
        (is (empty? (v/prove kb (list tagged (list FruitFn '?t)) 'CxUniverse))
            "a goal naming the application answers nothing"))
      (let [c (v/assert kb (list 'functionCorrespondingPredicate FruitFn fruitOf 2) 'CxUniverse)]
        (testing "the correspondence arrives: the rule is respelled and fires"
          (is (ripe?))
          (is (= [false true] [(names? kb h FruitFn) (names? kb h fruitOf)])))
        (v/retract! kb c)
        (testing "the correspondence leaves: the rule is as written and held again"
          (is (not (ripe?)))
          (is (= [true false] [(names? kb h FruitFn) (names? kb h fruitOf)])))))))

;; ---- every believed correspondence, as a union ---------------------------

(tu/deftest-kb a-fixed-and-a-variable-functor-goal-answer-with-a-minted-and-a-stated-value-in-every-order
  ;; the three goals answer alike whether the value is the constant the mint names or a
  ;; term the KB states, whichever of the mark, the correspondence and the facts arrive first
  (doseq [value [:minted :stated]
          order (orders [:mark :corr :facts])]
    (tu/with-terms [FruitFn AppleTree Gala Ann favoriteFood fruitOf]
      (let [steps {:mark  [(list 'reifiable_function FruitFn)]
                   :corr  [(list 'functionCorrespondingPredicate FruitFn fruitOf 2)]
                   :facts (if (= value :minted)
                            [(list favoriteFood Ann (list FruitFn AppleTree))]
                            [(list fruitOf AppleTree Gala) (list favoriteFood Ann Gala)])}]
        (doseq [step order] (run! #(v/assert kb % 'CxUniverse) (steps step)))
        (let [food (if (= value :minted) (nat-read/dedup-constant kb (list FruitFn AppleTree)) Gala)]
          (doseq [engine [:dfs :inference]]
            (is (= [#{{'?tree AppleTree}}
                    #{{'?fn FruitFn}}
                    #{{'?food food '?tree AppleTree '?fn FruitFn}}]
                   [(answers kb engine (list favoriteFood Ann (list FruitFn '?tree)) ['?tree])
                    (answers kb engine (list favoriteFood Ann (list '?fn AppleTree)) ['?fn])
                    (answers kb engine (list 'and (list 'equals '?food (list FruitFn '?tree))
                                             (list 'equals '?food (list '?fn AppleTree))
                                             (list favoriteFood Ann '?food))
                             ['?food '?tree '?fn])])
                (str value " " order " " engine))))))))

(tu/deftest-kb a-goal-answers-through-every-believed-correspondence
  (tu/with-terms [FruitFn AppleTree PearTree Gala Bosc Ann favoriteFood fruitOf producesFruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (run! #(v/assert kb % 'CxUniverse)
          [(list 'functionCorrespondingPredicate FruitFn fruitOf 2)
           (list 'functionCorrespondingPredicate FruitFn producesFruit 2)
           (list fruitOf AppleTree Gala) (list producesFruit PearTree Bosc)
           (list favoriteFood Ann Gala) (list favoriteFood Ann Bosc)])
    (doseq [engine [:dfs :inference]]
      (is (= [#{{'?tree AppleTree} {'?tree PearTree}}
              #{{'?fn FruitFn '?tree AppleTree} {'?fn FruitFn '?tree PearTree}}]
             [(answers kb engine (list favoriteFood Ann (list FruitFn '?tree)) ['?tree])
              (answers kb engine (list favoriteFood Ann (list '?fn '?tree)) ['?fn '?tree])])
          (str engine)))))

(tu/deftest-kb a-variable-functor-goal-reads-every-value-position
  ;; one conjunction per declaration shape, merged: position 1 and position 2
  (tu/with-terms [StreetCornerFn FruitFn Lot Xing North AppleTree Gala Bob owns streetCornerOf fruitOf]
    (run! #(v/assert kb % 'CxUniverse)
          [(list 'reifiable_function StreetCornerFn) (list 'reifiable_function FruitFn)
           (list 'functionCorrespondingPredicate StreetCornerFn streetCornerOf 1)
           (list 'functionCorrespondingPredicate FruitFn fruitOf 2)
           (list streetCornerOf Lot Xing North) (list owns Bob Lot)
           (list fruitOf AppleTree Gala) (list owns Bob Gala)])
    (doseq [engine [:dfs :inference]]
      (is (= [#{{'?fn StreetCornerFn}} #{{'?fn FruitFn}}]
             [(answers kb engine (list owns Bob (list '?fn Xing North)) ['?fn])
              (answers kb engine (list owns Bob (list '?fn AppleTree)) ['?fn])])
          (str engine)))
    (testing "an entry point that merges no answers refuses the union"
      (is (= :shape (:type (ex-data (try (v/query-status kb (list owns Bob (list '?fn Xing North))
                                                         'CxUniverse {:max-depth 2})
                                         (catch clojure.lang.ExceptionInfo e e)))))))))

(tu/deftest-kb a-rule-is-stored-once-per-believed-correspondence-in-every-order
  (doseq [order (orders [:fruit :produces :rule :facts])]
    (tu/with-terms [FruitFn AppleTree PearTree Gala Bosc tagged ripe fruitOf producesFruit]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (let [steps {:fruit    [(list 'functionCorrespondingPredicate FruitFn fruitOf 2)]
                   :produces [(list 'functionCorrespondingPredicate FruitFn producesFruit 2)]
                   :rule     [(list 'set/forwardRule
                                    (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t)))]
                   :facts    [(list fruitOf AppleTree Gala) (list tagged Gala)
                              (list producesFruit PearTree Bosc) (list tagged Bosc)]}
            hs    (into {} (map (fn [step] [step (mapv #(v/assert kb % 'CxUniverse) (steps step))])) order)
            ripe? #(set (map '?t (v/query kb (list ripe '?t) 'CxUniverse)))]
        (is (= #{AppleTree PearTree} (ripe?)) (str order " both"))
        (is (= #{AppleTree PearTree} (set (map '?t (answers kb :dfs (list ripe '?t) ['?t]))))
            (str order " backward"))
        (v/retract! kb (first (:produces hs)))
        (is (= #{AppleTree} (ripe?)) (str order " the producesFruit spelling leaves with its declaration"))
        (v/retract! kb (first (:fruit hs)))
        (is (= #{} (ripe?)) (str order " no correspondence: held"))))))

(tu/deftest-kb a-correspondence-respells-a-rule-and-a-goal-only-where-its-context-is-seen
  ;; the declaration is in CxSide; CxLow sees it, CxUniverse does not
  (tu/with-terms [FruitFn AppleTree Gala Ann tagged ripe fruitOf favoriteFood CxSide CxLow]
    (run! #(v/assert kb % 'CxUniverse {:strength :monotonic})
          [(list 'genlCx CxSide 'CxUniverse) (list 'genlCx CxLow CxSide)
           (list 'reifiable_function FruitFn)])
    (v/assert kb (list 'functionCorrespondingPredicate FruitFn fruitOf 2) CxSide)
    (run! #(v/assert kb % 'CxUniverse)
          [(list fruitOf AppleTree Gala) (list tagged Gala) (list favoriteFood Ann Gala)])
    (let [rule (list 'set/forwardRule (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t)))
          top  (v/assert kb rule 'CxUniverse)
          low  (v/assert kb rule CxLow)
          goal (list favoriteFood Ann (list FruitFn '?tree))]
      (testing "a reader that cannot see the declaration: the rule is held, the goal answers nothing"
        (is (= [true false] [(names? kb top FruitFn) (names? kb top fruitOf)]))
        (is (= [false :inert] ((juxt :believed? :reason) (v/why-not kb top))))
        (is (not (v/ask? kb (list ripe AppleTree) 'CxUniverse)))
        (is (= #{} (answers kb :dfs goal ['?tree]) (answers kb :inference goal ['?tree]))))
      (testing "the held rule is respelled where its context and the declaration's meet"
        (is (v/ask? kb (list ripe AppleTree) CxSide)))
      (testing "a reader below the declaration's context: the rule is respelled, the goal answers"
        (is (= [false true] [(names? kb low FruitFn) (names? kb low fruitOf)]))
        (is (v/ask? kb (list ripe AppleTree) CxLow))
        (is (= #{{'?tree AppleTree}} (answers kb :dfs goal ['?tree] CxSide)
               (answers kb :inference goal ['?tree] CxLow)))))))

(def ^:private meet-variants
  "The rule's context, the `genlCx` edge step and the readers' answers in `meet-readers`
  order with the edge and after it leaves.  Fixed edges: CxSide, CxLow under CxUniverse,
  CxBoth under CxLow; the declaration is in CxSide."
  {:low  {:rule :low  :edge [:low :side]  :with [true false true false]  :without [false false false false]}
   :top  {:rule :top  :edge [:low :side]  :with [true true true false]   :without [false true false false]}
   :meet {:rule :low  :edge [:both :side] :with [false false true false] :without [false false false false]}})

(defn- meet-run!
  "Assert the `variant` ingredients of `meet-variants` in `order` on `kb` and answer
  `{:hs {step [handle …]} :row (fn [] [ripe-per-reader goal-at-CxBoth])}`."
  [kb variant order {:keys [FruitFn AppleTree Gala Ann tagged ripe fruitOf favoriteFood CxSide CxLow CxBoth]}]
  (let [cx    {:low CxLow :side CxSide :both CxBoth :top 'CxUniverse}
        {:keys [rule edge]} (meet-variants variant)]
    (run! #(v/assert kb % 'CxUniverse {:strength :monotonic})
          [(list 'genlCx CxSide 'CxUniverse) (list 'genlCx CxLow 'CxUniverse) (list 'genlCx CxBoth CxLow)
           (list 'reifiable_function FruitFn)])
    (let [steps {:corr  [[(list 'functionCorrespondingPredicate FruitFn fruitOf 2) CxSide]]
                 :rule  [[(list 'set/forwardRule
                                (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t)))
                          (cx rule)]]
                 :facts [[(list fruitOf AppleTree Gala) 'CxUniverse] [(list tagged Gala) 'CxUniverse]
                         [(list favoriteFood Ann Gala) 'CxUniverse]]
                 :edge  [[(list 'genlCx (cx (first edge)) (cx (second edge))) 'CxUniverse]]}]
      {:hs  (into {} (map (fn [step] [step (mapv (fn [[s c]] (v/assert kb s c {:strength :monotonic}))
                                                 (steps step))]))
                  order)
       :row #(vector (mapv (fn [c] (v/ask? kb (list ripe AppleTree) c)) [CxLow CxSide CxBoth 'CxUniverse])
                     (answers kb :dfs (list favoriteFood Ann (list FruitFn '?tree)) ['?tree] CxBoth))})))

(tu/deftest-kb a-correspondence-respells-a-rule-where-its-context-meets-the-declarations-in-every-order
  ;; the declaration, the rule, the facts and an edge, in all 24 orders, for a rule below
  ;; the declaration's context once the edge is in, a rule in CxUniverse, and a rule whose
  ;; context meets the declaration's only in CxBoth; then the edge leaves
  (doseq [variant (keys meet-variants)
          order   (orders [:corr :rule :facts :edge])]
    (tu/with-terms [FruitFn AppleTree Gala Ann tagged ripe fruitOf favoriteFood CxSide CxLow CxBoth]
      (let [{:keys [hs row]} (meet-run! kb variant order {:FruitFn FruitFn :AppleTree AppleTree :Gala Gala
                                                          :Ann Ann :tagged tagged :ripe ripe :fruitOf fruitOf
                                                          :favoriteFood favoriteFood :CxSide CxSide
                                                          :CxLow CxLow :CxBoth CxBoth})
            {:keys [with without]} (meet-variants variant)]
        (is (= [with #{{'?tree AppleTree}}] (row)) (str variant " " order))
        (v/retract! kb (first (:edge hs)))
        (is (= [without #{}] (row)) (str variant " " order " the edge leaves"))))))

(tu/deftest-kb a-correspondence-meet-respelling-leaves-with-each-ingredient
  (doseq [variant (keys meet-variants)
          gone    [:corr :rule :facts :edge]]
    (tu/with-terms [FruitFn AppleTree Gala Ann tagged ripe fruitOf favoriteFood CxSide CxLow CxBoth]
      (let [{:keys [hs row]} (meet-run! kb variant [:rule :facts :corr :edge]
                                        {:FruitFn FruitFn :AppleTree AppleTree :Gala Gala :Ann Ann
                                         :tagged tagged :ripe ripe :fruitOf fruitOf :favoriteFood favoriteFood
                                         :CxSide CxSide :CxLow CxLow :CxBoth CxBoth})
            {:keys [without]} (meet-variants variant)]
        (run! #(v/retract! kb %) (gone hs))
        (is (= (case gone :edge [without #{}] :rule [[false false false false] #{{'?tree AppleTree}}]
                     [[false false false false] #{}])
               (row))
            (str variant " without " gone))))))

(tu/deftest-kb recover-stores-the-meet-spelling-a-store-without-it-lacks
  ;; the write stores no meet spelling, as a store written before a held rule stored one
  ;; holds none; `recover` adds it, and the teardown of the rule removes it
  (tu/with-terms [FruitFn AppleTree Gala tagged ripe fruitOf CxSide]
    (run! #(v/assert kb % 'CxUniverse {:strength :monotonic})
          [(list 'genlCx CxSide 'CxUniverse) (list 'reifiable_function FruitFn)
           (list fruitOf AppleTree Gala) (list tagged Gala)])
    (with-redefs-fn {(ns-resolve 'vaelii.impl.chain 'rule-correspondence-want) (constantly nil)}
      #(do (v/assert kb (list 'functionCorrespondingPredicate FruitFn fruitOf 2) CxSide)
           (v/assert kb (list 'set/forwardRule (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t)))
                     'CxUniverse)))
    (is (not (v/ask? kb (list ripe AppleTree) CxSide)) "the store holds no meet spelling")
    (v/recover kb)
    (is (v/ask? kb (list ripe AppleTree) CxSide))
    (is (not (v/ask? kb (list ripe AppleTree) 'CxUniverse)))))

(tu/deftest-kb a-rule-holding-a-variable-functor-application-is-held
  (tu/with-terms [FruitFn AppleTree Gala Rex Ann tagged ripe fruitOf dog heard]
    (run! #(v/assert kb % 'CxUniverse)
          [(list 'reifiable_function FruitFn) (list 'functionCorrespondingPredicate FruitFn fruitOf 2)
           (list fruitOf AppleTree Gala) (list tagged Gala)
           (list 'set/forwardRule (list 'implies (list tagged (list '?fn '?t)) (list ripe '?t)))])
    (is (empty? (v/query kb (list ripe '?t) 'CxUniverse)) "the rule fires nothing")
    (testing "a variable-functor compound in a formula position is a sentence pattern"
      (v/assert kb (list 'believes Ann (list dog Rex)) 'CxUniverse)
      (v/assert kb (list 'set/forwardRule (list 'implies (list 'believes '?a (list '?p Rex)) (list heard '?a '?p)))
                'CxUniverse)
      (is (true? (v/ask? kb (list heard Ann dog) 'CxUniverse)))
      (is (= #{{'?p dog}} (answers kb :dfs (list 'believes Ann (list '?p Rex)) ['?p]))))))

(tu/deftest-kb a-modal-proposition-keeps-its-applications-as-written-on-every-path-in-every-order
  ;; the rule over Ann's belief and the goals read the proposition as written, the Bob
  ;; firing stores the asserted spelling, and with no correspondence only the rule whose
  ;; application sits outside a proposition is held
  (doseq [corr? [true false]
          order (orders (cond-> [:rules :facts] corr? (conj :corr)))]
    (tu/with-terms [FruitFn Ann Bob Apple Pear likes fanOf admires tagged fruitOf]
      (let [bob   (list 'believes Bob (list likes Bob (list FruitFn Pear)))
            steps {:corr  [(list 'functionCorrespondingPredicate FruitFn fruitOf 2)]
                   :rules [(list 'set/forwardRule
                                 (list 'implies (list tagged (list FruitFn '?t))
                                       (list 'believes Bob (list likes Bob (list FruitFn '?t)))))
                           (list 'set/forwardRule
                                 (list 'implies (list 'believes '?a (list likes '?a (list FruitFn '?t)))
                                       (list fanOf '?a '?t)))
                           (list 'implies (list 'believes '?a (list likes '?a (list FruitFn '?t)))
                                 (list admires '?a '?t))]
                   :facts [(list tagged (list FruitFn Pear))
                           (list 'believes Ann (list likes Ann (list FruitFn Apple)))]}
            _     (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
            hs    (into {} (map (fn [step] [step (mapv #(v/assert kb % 'CxUniverse) (steps step))])) order)
            at    (str corr? " " (vec order))
            fans  (set (map :sentence (v/sentexes-matching kb (list fanOf '?a '?t) 'CxUniverse)))
            bobs  (v/sentexes-matching kb (list 'believes Bob '?p) 'CxUniverse)]
        (is (= (cond-> #{(list fanOf Ann Apple)} corr? (conj (list fanOf Bob Pear))) fans)
            (str at " the rule over a belief matches the stored belief"))
        (is (= (if corr? [bob] []) (mapv :sentence bobs)) (str at " the firing stores the proposition as written"))
        (is (= corr? (v/ask? kb bob 'CxUniverse)) (str at " ask"))
        (doseq [engine [:dfs :inference]]
          (is (= #{{'?t Apple}}
                 (answers kb engine (list 'believes Ann (list likes Ann (list FruitFn '?t))) ['?t]))
              (str at " " engine " goal"))
          (is (= (cond-> #{{'?a Ann '?t Apple}} corr? (conj {'?a Bob '?t Pear}))
                 (answers kb engine (list admires '?a '?t) ['?a '?t]))
              (str at " " engine " backward rule")))
        (is (not= :inert (:reason (v/why-not kb (second (:rules hs)))))
            (str at " a rule whose only application is in a proposition is not held"))
        (when corr?
          (is (= (:id (first bobs)) (v/assert kb bob 'CxUniverse))
              (str at " the asserted and the derived belief are one sentex")))))))

(tu/deftest-kb a-formula-declaration-releases-a-held-variable-functor-rule-in-every-order
  ;; the declaration types holdsIn's second position `sentence` directly, or `note` that a
  ;; `genl` edge puts under it; the last removal holds the rules again
  (doseq [via   [:direct :genl]
          order (orders (cond-> [:arg :rules :fact] (= via :genl) (conj :genl)))]
    (tu/with-terms [Doc Rex dog note holdsIn heardOf toldOf]
      (let [steps {:arg   [(list 'arg holdsIn 2 (if (= via :genl) note 'sentence))]
                   :genl  [(list 'genl note 'sentence)]
                   :rules [(list 'set/forwardRule
                                 (list 'implies (list holdsIn '?c (list '?p Rex)) (list heardOf '?c '?p)))
                           (list 'implies (list holdsIn '?c (list '?p Rex)) (list toldOf '?c '?p))]
                   :fact  [(list holdsIn Doc (list dog Rex))]}
            hs    (into {} (map (fn [step] [step (mapv #(v/assert kb % 'CxUniverse) (steps step))])) order)
            ;; the forward rule's answers, the backward rule's, and the stored firings
            reads #(vector (set (v/query kb (list heardOf '?c '?p) 'CxUniverse))
                           (answers kb :dfs (list toldOf '?c '?p) ['?c '?p])
                           (into #{} (filter (fn [s] (and (seq? s) (= heardOf (first s)))))
                                 (stored-sentences kb)))
            live  [#{{'?c Doc '?p dog}} #{{'?c Doc '?p dog}} #{(list heardOf Doc dog)}]]
        (is (= live (reads)) (str via " " order " live"))
        (when (= via :genl)
          (v/retract! kb (first (:genl hs)))
          (is (= [#{} #{} #{}] (reads)) (str order " the genl edge leaves: held"))
          (v/assert kb (first (steps :genl)) 'CxUniverse)
          (is (= live (reads)) (str order " the genl edge returns: live")))
        (v/retract! kb (first (:arg hs)))
        (is (= [#{} #{} #{}] (reads)) (str via " " order " the declaration leaves: held"))))))

(tu/deftest-kb a-formula-declaration-respells-a-rule-holding-a-variable-functor-and-a-fixed-application
  ;; with `(?p ?x)` in a term position the whole rule stays as written and held; in a
  ;; formula position FruitFn's application is respelled through fruitOf
  (tu/with-terms [FruitFn AppleTree Gala Doc dog holdsIn tagged heardOf fruitOf]
    (run! #(v/assert kb % 'CxUniverse)
          [(list 'reifiable_function FruitFn) (list 'functionCorrespondingPredicate FruitFn fruitOf 2)
           (list fruitOf AppleTree Gala) (list tagged Gala) (list holdsIn Doc (list dog AppleTree))])
    (let [h     (v/assert kb (list 'set/forwardRule
                                   (list 'implies (list 'and (list holdsIn '?c (list '?p '?x)) (list tagged (list FruitFn '?x)))
                                         (list heardOf '?c '?p)))
                          'CxUniverse)
          state #(vector (v/query kb (list heardOf '?c '?p) 'CxUniverse) (names? kb h fruitOf))]
      (is (= [[] false] (state)) "held as written")
      (let [d (v/assert kb (list 'arg holdsIn 2 'formula) 'CxUniverse)]
        (is (= [[{'?c Doc '?p dog}] true] (state)) "released and respelled")
        (v/retract! kb d)
        (is (= [[] false] (state)) "held as written again")))))

;; ---- an application that was never minted --------------------------------

(tu/deftest-kb a-never-minted-application-in-a-goal-equals-only-itself-and-its-congruent-spellings
  ;; `no-match` names no term: no equality, `different` or taxonomy reading answers it.
  ;; An equation keeps the application as written, so identity and congruence answer.
  (tu/with-terms [FooFn BarFn BazFn Xa Xb Xc Xd Ann Bob Zed CxA fooOf likes twin tag]
    (let [app   (fn [& args] (apply list FooFn args))
          reads (fn [goal cx] (mapv #(set (% kb goal cx)) [v/ask v/prove v/query]))
          check (fn [stage rows]
                  (doseq [[goal cx want] rows]
                    (is (= [want want want] (reads goal cx)) (str stage " " (pr-str goal) " in " cx))))
          ab    (app Xa Xb)
          cd    (app Xc Xd)]
      (v/assert kb (list 'reifiable_function FooFn) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (check :unminted
             [[(list 'equals ab cd) CxA #{}]
              [(list 'equals ab ab) CxA #{{}}]
              [(list 'equals (app Ann Bob) cd) CxA #{}]
              [(list 'equals '?x ab) CxA #{}]
              [(list 'genl ab '?y) CxA #{}]
              [(list 'equals (app '?a Xb) (app '?c Xd)) CxA #{}]
              [(list 'different ab Zed) CxA #{}]
              [(list 'different (list BarFn ab) Zed) CxA #{}]
              [(list 'equals (list BarFn ab) (list BarFn cd)) CxA #{}]
              [(list 'equals (list BarFn ab) (list BarFn ab)) CxA #{{}}]
              [(list 'equals '?x (list BarFn ab)) CxA #{}]
              [(list 'genl (list BarFn ab) '?y) CxA #{}]
              [(list 'different (list BazFn (list BarFn ab)) Zed) CxA #{}]
              [(list 'equals (list BazFn (list BarFn ab)) (list BazFn (list BarFn cd))) CxA #{}]
              [(list 'not (list 'different ab Zed)) CxA #{}]
              [(list 'not (list 'different (list BarFn ab) Zed)) CxA #{}]])
      (v/assert kb (list tag Zed) 'CxUniverse)
      (let [naf [(list tag '?z) (list 'unknown (list tag ab))]]
        (is (= [#{{'?z Zed}} #{{'?z Zed}}] (mapv #(set (% kb naf CxA)) [v/prove v/query]))
            "an unknown's sentence"))
      (v/assert kb (list likes Ann (app Ann Bob)) 'CxUniverse)
      (let [k (nat-read/dedup-constant kb (app Ann Bob))]
        (check :minted
               [[(list 'equals (app Ann Bob) cd) CxA #{}]
                [(list 'equals (app Ann Bob) (app Ann Bob)) CxA #{{}}]
                [(list 'equals '?x (app Ann Bob)) CxA #{{'?x k}}]]))
      (v/assert kb (list 'equals Xa Xc) CxA)
      (v/assert kb (list 'equals Xb Xd) CxA)
      (check :congruent
             [[(list 'equals ab cd) CxA #{{}}]
              [(list 'equals ab cd) 'CxUniverse #{}]])
      (v/assert kb (list 'functionCorrespondingPredicate FooFn fooOf 3) 'CxUniverse)
      (check :corresponded
             [[(list 'equals ab (app Ann Bob)) CxA #{}]
              [(list 'equals ab cd) 'CxUniverse #{}]
              [(list 'equals ab ab) 'CxUniverse #{{}}]])
      (v/assert kb (list 'implies (list 'equals (app Zed Xb) (app Xc Xd)) (list twin Zed)) 'CxUniverse)
      (is (empty? (v/prove kb (list twin '?z) 'CxUniverse)) "a rule antecedent"))))

;; ---- a correspondence value is read where it is visible -------------------

(defn- on-own-kb
  "`(f kb)` on an empty KB of its own, cleared after."
  [f]
  (let [kb (tu/isolated-fresh)]
    (try (f kb) (finally (tu/clear-kb! kb)))))

(defn- commuted-mints
  "`[constants equalities-in-CxParent]` after the six sentences with `names` for the
  four individuals, the two `equals` in CxA in written order or `reversed?`."
  [kb [a b c d] reversed?]
  (let [m  {:strength :monotonic}
        e1 (list 'equals (list 'fooFn c b) (list 'fooFn b a))
        e2 (list 'equals (list 'fooFn d a) (list 'fooFn a b))]
    (doseq [[s cx] '[[(reifiable_function fooFn) CxUniverse] [(binary_function fooFn) CxUniverse]
                     [(functionCorrespondingPredicate fooFn fooOf 3) CxUniverse]
                     [(genlCx CxParent CxUniverse) CxParent] [(ternary_predicate fooOf) CxParent]
                     [(commutativeInArgs fooOf 1 2) CxParent] [(functionalInArg fooOf 3) CxParent]
                     [(genlCx CxA CxParent) CxParent]]]
      (v/assert kb s cx m))
    (doseq [e (if reversed? [e2 e1] [e1 e2])] (v/assert kb e 'CxA m))
    [(count (distinct (map '?k (v/ask kb '(natFormula ?k ?e) 'CxUniverse))))
     (count (v/sentexes-matching kb '(equals ?x ?y) 'CxParent))]))

(deftest a-commuted-application-reifies-to-the-value-the-writer-reads-for-every-name-and-order
  ;; a merge's restatement of a corresponding fact in CxA is no second value for a
  ;; writer that reads it as the same term
  (doseq [names '[[n/Aa n/Bb n/Cc n/Dd] [Aa Bb Cc Dd] [P2x0 P2x1 P2x2 P2x3] [P1x0 P1x1 P1x2 P1x3]]
          rev?  [false true]]
    (is (= [3 0] (on-own-kb #(commuted-mints % names rev?))) (pr-str names rev?))))

(deftest a-merge-the-writer-does-not-see-leaves-one-value
  ;; with `Maria` the merge in CxB restates `(momOf Muffet Mary)` there; with `Mz` it
  ;; restates nothing, since `Mary` stays the representative
  (doseq [other '[Maria Mz]]
    (is (= '[(tagged Mary)]
           (on-own-kb (fn [kb]
                        (run! (fn [[s cx & opts]] (apply v/assert kb s cx opts))
                              [['(reifiable_function MomFn) 'CxUniverse]
                               ['(functionCorrespondingPredicate MomFn momOf 2) 'CxUniverse]
                               ['(genlCx CxB CxUniverse) 'CxUniverse]
                               ['(momOf Muffet Mary) 'CxUniverse {:strength :monotonic}]
                               [(list 'equals 'Mary other) 'CxB]
                               ['(tagged (MomFn Muffet)) 'CxUniverse]])
                        (mapv :sentence (v/sentexes-matching kb '(tagged ?x) 'CxUniverse)))))
        (str other))))

(deftest a-value-in-a-context-retires-the-placeholder-there-alone-in-every-order
  (doseq [order (orders [:decl :fact :use :edge])]
    (is (= {:story true :universe false :placeholder 1}
           (on-own-kb
            (fn [kb]
              (v/assert kb '(reifiable_function MomFn) 'CxUniverse)
              (doseq [step order]
                (case step
                  :decl (v/assert kb '(functionCorrespondingPredicate MomFn momOf 2) 'CxUniverse)
                  :fact (v/assert kb '(momOf Muffet Mary) 'CxStory)
                  :use  (v/assert kb '(caresFor Bob (MomFn Muffet)) 'CxUniverse)
                  :edge (v/assert kb '(genlCx CxStory CxUniverse) 'CxUniverse)))
              {:story       (v/ask? kb '(caresFor Bob Mary) 'CxStory)
               :universe    (v/ask? kb '(caresFor Bob Mary) 'CxUniverse)
               :placeholder (count (filter #(nat-read/reified-nat-symbol? (get % '?m))
                                           (v/ask kb '(momOf Muffet ?m) 'CxUniverse)))})))
        (pr-str order))))

;; ---- a :default value copies the uses of the placeholder -------------------

(defn- believed-content
  "Every believed sentex's `[sentence context]`, as a set."
  [kb]
  (into #{} (map #(let [s (v/sentex kb %)] [(v/sentence-of s) (:context s)]))
        (v/believed kb (tu/sentex-ids kb))))

(defn- default-value-step!
  "Write `step` of the `:default` value scenario over `terms`: the declaration, the
  `:default` fact and a use of the value in CxStory, a use of the application in
  CxUniverse, or a forward and a backward rule naming the application."
  [kb [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory] step]
  (let [app (list MomFn Muffet)]
    (case step
      :decl  (v/assert kb (list 'functionCorrespondingPredicate MomFn momOf 2) 'CxUniverse)
      :fact  (do (v/assert kb (list momOf Muffet Mary) CxStory)
                 (v/assert kb (list likes Ann Mary) CxStory))
      :use   (v/assert kb (list likes Tom app) 'CxUniverse)
      :rules (do (v/assert kb (list 'set/forwardRule (list 'implies (list likes '?x app) (list fond '?x)))
                           'CxUniverse)
                 (v/assert kb (list 'implies (list likes '?x app) (list warm '?x)) 'CxUniverse)))))

(defn- default-value-kb!
  "The mark and `(genlCx CxStory CxUniverse)`, then `steps` (`default-value-step!`)."
  [kb [MomFn _ _ _ _ _ _ _ _ CxStory :as terms] steps]
  (v/assert kb (list 'reifiable_function MomFn) 'CxUniverse {:strength :monotonic})
  (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse {:strength :monotonic})
  (run! #(default-value-step! kb terms %) steps))

(defn- rule-answers
  "`{:fond … :warm …}`: what the forward and the backward rule answer in `ctx`."
  [kb [_ _ _ _ _ _ _ fond warm] ctx]
  {:fond (answers kb :dfs (list fond '?x) ['?x] ctx)
   :warm (answers kb :dfs (list warm '?x) ['?x] ctx)})

(deftest a-default-value-reads-the-same-in-every-order
  (tu/with-terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
    (let [terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
          runs  (for [order (orders [:decl :fact :use :rules])]
                  (on-own-kb (fn [kb]
                               (default-value-kb! kb terms order)
                               {:content  (believed-content kb)
                                :story    (rule-answers kb terms CxStory)
                                :universe (rule-answers kb terms 'CxUniverse)})))]
      (is (= 1 (count (set (map :content runs)))) "one believed set")
      (is (= #{{:story    {:fond #{{'?x Ann} {'?x Tom}} :warm #{{'?x Ann} {'?x Tom}}}
                :universe {:fond #{{'?x Tom}} :warm #{{'?x Tom}}}}}
             (set (map #(dissoc % :content) runs)))
          "the forward and the backward rule answer alike in both contexts"))))

(tu/deftest-kb a-default-value-copies-the-uses-and-the-rules-and-merges-nothing
  (tu/with-terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
    (let [terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
          _     (default-value-kb! kb terms [:decl :fact :use :rules])
          k     (nat-read/dedup-constant kb (list MomFn Muffet))
          held  (believed-content kb)]
      (is (nat-read/reified-object-symbol? k))
      (is (= #{[(list likes Tom k) 'CxUniverse] [(list likes Tom Mary) CxStory]}
             (into #{} (filter #(= likes (ffirst %))) (filter #(= Tom (second (first %))) held))))
      (is (contains? held [(list momOf Muffet k) 'CxUniverse]))
      (is (v/believed? kb (v/handle-of kb (list 'implies (list likes '?x Mary) (list fond '?x)) CxStory) CxStory))
      (is (not-any? #(= 'rewriteOf (ffirst %)) (filter #(seq? (first %)) held))))))

(tu/deftest-kb a-default-value-defeated-takes-every-copy-out
  (tu/with-terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
    (let [terms  [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
          _      (default-value-kb! kb terms [:decl :fact :use :rules])
          denial (v/assert kb (list 'not (list momOf Muffet Mary)) CxStory {:strength :monotonic})
          mary   (fn [] (into #{} (filter #(some #{Mary} (tree-seq sequential? seq (first %))))
                              (believed-content kb)))]
      (is (= #{[(list likes Ann Mary) CxStory] [(list 'not (list momOf Muffet Mary)) CxStory]} (mary)))
      (is (= {:fond #{{'?x Tom}} :warm #{{'?x Tom}}} (rule-answers kb terms CxStory)))
      (v/retract! kb denial)
      (is (contains? (mary) [(list likes Tom Mary) CxStory]))
      (is (= {:fond #{{'?x Ann} {'?x Tom}} :warm #{{'?x Ann} {'?x Tom}}} (rule-answers kb terms CxStory))))))

;; a `defeat` or `contradicts` names handles, which vary with the order
(defn- unnamed-content
  "`believed-content` with each `(sentexHandle h)` replaced by `h`'s `[sentence context]`."
  [kb]
  (letfn [(unname [x]
            (cond (and (seq? x) (= 'sentexHandle (first x)))
                  (if-let [s (v/sentex kb (second x))] [(unname (v/sentence-of s)) (:context s)] x)
                  (seq? x) (map unname x)
                  :else x))]
    (into #{} (map (fn [[s c]] [(unname s) c])) (believed-content kb))))

(defn- rival-value-kb
  "The mark and `(genlCx CxStory CxUniverse)`, then `steps` of the two-value scenario:
  the declaration, the `:default` values `Mary` and `Jane` in CxStory, a `:monotonic`
  denial of `Jane` there (`:deny`) or an `except` of `Jane`'s fact there (`:exc`, after
  `:jane`), a use of the application in CxUniverse, and an `except` of the use in CxStory
  (`:exc-use`, after `:use`).  Returns the handles the steps wrote, by step."
  [kb [MomFn momOf Muffet Mary Jane Tom likes CxStory] steps]
  (v/assert kb (list 'reifiable_function MomFn) 'CxUniverse {:strength :monotonic})
  (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse {:strength :monotonic})
  (reduce (fn [hs step]
            (assoc hs step
                   (case step
                     :decl (v/assert kb (list 'functionCorrespondingPredicate MomFn momOf 2) 'CxUniverse)
                     :mary (v/assert kb (list momOf Muffet Mary) CxStory)
                     :jane (v/assert kb (list momOf Muffet Jane) CxStory)
                     :deny (v/assert kb (list 'not (list momOf Muffet Jane)) CxStory {:strength :monotonic})
                     :exc  (v/assert kb (list 'except (list 'sentexHandle (:jane hs))) CxStory
                                     {:strength :monotonic})
                     :use  (v/assert kb (list likes Tom (list MomFn Muffet)) 'CxUniverse)
                     :exc-use (v/assert kb (list 'except (list 'sentexHandle (:use hs))) CxStory
                                        {:strength :monotonic}))))
          {} steps))

(defn- rival-value-orders
  "Every order of the steps with `rival`, `:deny` or `:exc`; `:exc` follows `:jane`,
  whose handle it names."
  [rival]
  (filterv #(or (= :deny rival) (< (.indexOf ^java.util.List % :jane) (.indexOf ^java.util.List % :exc)))
           (map vec (orders [:decl :mary :jane rival :use]))))

(defn- rival-value-runs
  "`{:content :copies}` after each of `orders` on a KB of its own: the believed set
  (`unnamed-content`), and whether CxStory believes the copy naming `Mary` and the one
  naming `Jane`."
  [orders]
  (tu/with-terms [MomFn momOf Muffet Mary Jane Tom likes CxStory]
    (let [terms [MomFn momOf Muffet Mary Jane Tom likes CxStory]]
      (doall
       (for [order orders]
         (on-own-kb (fn [kb]
                      (rival-value-kb kb terms order)
                      {:content (unnamed-content kb)
                       :copies  [(v/ask? kb (list likes Tom Mary) CxStory)
                                 (v/ask? kb (list likes Tom Jane) CxStory)]})))))))

(deftest ^:slow a-default-value-whose-rival-is-defeated-or-excepted-takes-its-copy-in-every-order
  (doseq [rival [:deny :exc]]
    (let [runs (rival-value-runs (rival-value-orders rival))]
      (is (= 1 (count (set (map :content runs)))) (str rival ": one believed set"))
      (is (= #{[true false]} (set (map :copies runs))) (str rival)))))

(deftest a-default-value-whose-rival-is-defeated-or-excepted-takes-its-copy-in-sampled-orders
  (doseq [orders [[[:decl :mary :jane :use :deny] [:use :jane :mary :deny :decl]
                   [:deny :mary :decl :jane :use] [:jane :deny :use :mary :decl]]
                  [[:decl :mary :jane :use :exc] [:use :mary :decl :jane :exc]
                   [:jane :exc :decl :use :mary] [:mary :jane :exc :use :decl]]]]
    (let [runs (rival-value-runs orders)]
      (is (= 1 (count (set (map :content runs)))) (str (peek (first orders)) ": one believed set"))
      (is (= #{[true false]} (set (map :copies runs))) (str (peek (first orders)))))))

(deftest a-use-whose-except-is-retracted-takes-its-copy-in-every-order
  (tu/with-terms [MomFn momOf Muffet Mary Jane Tom likes CxStory]
    (let [terms [MomFn momOf Muffet Mary Jane Tom likes CxStory]
          copy  (list likes Tom Mary)
          runs  (for [order (map vec (orders [:decl :mary :use :exc-use]))
                      :when (< (.indexOf ^java.util.List order :use) (.indexOf ^java.util.List order :exc-use))]
                  (on-own-kb (fn [kb]
                               (let [hs   (rival-value-kb kb terms order)
                                     with [(v/ask? kb copy CxStory) (unnamed-content kb)]]
                                 (v/retract! kb (:exc-use hs))
                                 {:with with :after [(v/ask? kb copy CxStory) (unnamed-content kb)]}))))]
      (is (= 12 (count runs)))
      (is (= 1 (count (set runs))) "one believed set with the except and one after it")
      (is (= [false true] (map #(first (get (first runs) %)) [:with :after]))
          "CxStory holds the copy once the except is retracted"))))

(tu/deftest-kb a-default-value-whose-rival-is-given-back-loses-its-copy
  (doseq [rival [:deny :exc]]
    (tu/with-terms [MomFn momOf Muffet Mary Jane Tom likes CxStory]
      (let [terms [MomFn momOf Muffet Mary Jane Tom likes CxStory]
            hs    (rival-value-kb kb terms [:decl :mary :jane rival :use])]
        (is (v/ask? kb (list likes Tom Mary) CxStory) (str rival))
        (v/retract! kb (get hs rival))
        (is (v/ask? kb (list momOf Muffet Jane) CxStory) (str rival))
        (is (not (v/ask? kb (list likes Tom Mary) CxStory)) (str rival))
        (is (not (v/ask? kb (list likes Tom Jane) CxStory)) (str rival))))))

(tu/deftest-kb a-context-that-does-not-see-a-default-value-reads-the-placeholder-only
  (tu/with-terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory CxOther]
    (let [terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]]
      (default-value-kb! kb terms [:decl :fact :use :rules])
      (v/assert kb (list 'genlCx CxOther 'CxUniverse) 'CxUniverse {:strength :monotonic})
      (is (empty? (v/ask kb (list likes '?x Mary) CxOther)))
      (is (= [(nat-read/dedup-constant kb (list MomFn Muffet))]
             (map '?m (v/ask kb (list momOf Muffet '?m) CxOther))))
      (is (v/ask? kb (list likes Tom (list MomFn Muffet)) CxOther))
      (is (= {:fond #{{'?x Tom}} :warm #{{'?x Tom}}} (rule-answers kb terms CxOther))))))

(tu/deftest-kb a-default-value-made-monotonic-and-default-again-ends-where-it-started
  (tu/with-terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
    (let [terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
          _     (default-value-kb! kb terms [:decl :fact :use :rules])
          start (believed-content kb)
          fact  (v/handle-of kb (list momOf Muffet Mary) CxStory)
          k     (nat-read/dedup-constant kb (list MomFn Muffet))]
      (v/assert kb (list momOf Muffet Mary) CxStory {:strength :monotonic})
      (is (contains? (believed-content kb) [(list 'rewriteOf Mary k) CxStory]))
      (is (= Mary (nat-read/correspondence-value kb (list MomFn Muffet) CxStory)))
      (v/retract! kb fact)
      (v/assert kb (list momOf Muffet Mary) CxStory)
      (is (= start (believed-content kb))))))

(deftest retracting-a-default-value-or-its-declaration-is-net-neutral
  (tu/with-terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]
    (let [terms [MomFn momOf Muffet Mary Tom Ann likes fond warm CxStory]]
      (doseq [[step written ctx] [[:fact (list momOf Muffet Mary) CxStory]
                                  [:decl (list 'functionCorrespondingPredicate MomFn momOf 2) 'CxUniverse]]]
        (is (on-own-kb
             (fn [kb]
               (default-value-kb! kb terms (concat [:use :rules] (remove #{step} [:decl :fact])))
               (v/assert kb (list likes Ann Mary) CxStory)
               (let [before (tu/baseline kb)]
                 (default-value-step! kb terms step)
                 (v/retract! kb (v/handle-of kb written ctx))
                 (= before (tu/baseline kb)))))
            (str step))))))

;; ---- an application resolves under the reader's merges ---------------------

(deftest an-application-resolves-under-the-merges-the-reader-sees
  (testing "a merge in CxUniverse does not reach an application read in a context that does not see it"
    (is (= [false false]
           (on-own-kb (fn [kb]
                        (v/assert kb '(reifiable_function FruitFn) 'CxUniverse)
                        (v/assert kb '(likes Tom (FruitFn Apple)) 'CxAgentAnn)
                        (v/assert kb '(likes Tom Apple) 'CxAgentAnn)
                        (v/assert kb '(sameAs Apple Pomme) 'CxUniverse)
                        [(v/ask? kb '(likes Tom (FruitFn Pomme)) 'CxAgentAnn)
                         (v/ask? kb '(likes Tom Pomme) 'CxAgentAnn)])))))
  (testing "a merge in the reader's own context reaches the application as it reaches the symbol"
    (is (= [true true]
           (on-own-kb (fn [kb]
                        (v/assert kb '(reifiable_function FruitFn) 'CxUniverse)
                        (v/assert kb '(genlCx CxOne CxUniverse) 'CxUniverse)
                        (v/assert kb '(likes Tom (FruitFn Apple)) 'CxOne)
                        (v/assert kb '(likes Tom Apple) 'CxOne)
                        (v/assert kb '(sameAs Apple Pomme) 'CxOne)
                        [(v/ask? kb '(likes Tom (FruitFn Pomme)) 'CxOne)
                         (v/ask? kb '(likes Tom Pomme) 'CxOne)]))))))

(deftest a-compound-rewriteof-resolves-an-application-only-where-its-context-is-seen
  ;; CxBelow sees CxStory, which states the rewriteOf; CxOther and CxUniverse do not
  (doseq [order [[:rewrite :facts] [:facts :rewrite]]]
    (is (= {:other-stored-as-target false :universe-stored-as-target false
            :other-reads false :universe-reads false :below-reads true}
           (on-own-kb
            (fn [kb]
              (v/assert kb '(reifiable_function MotherFn) 'CxUniverse)
              (doseq [[c p] '[[CxStory CxUniverse] [CxBelow CxStory] [CxOther CxUniverse]]]
                (v/assert kb (list 'genlCx c p) 'CxUniverse))
              (doseq [step order]
                (case step
                  :rewrite (v/assert kb '(rewriteOf Mary (MotherFn Muffet)) 'CxStory)
                  :facts   (do (v/assert kb '(hates Tom Mary) 'CxUniverse)
                               (v/assert kb '(likes Tom (MotherFn Muffet)) 'CxOther)
                               (v/assert kb '(admires Tom (MotherFn Muffet)) 'CxUniverse))))
              (let [stored-as-target? (fn [pat cx]
                                        (= ['Mary] (map #(nth (:sentence %) 2)
                                                        (v/sentexes-matching kb pat cx))))
                    reads?            #(v/ask? kb '(hates Tom (MotherFn Muffet)) %)]
                {:other-stored-as-target    (stored-as-target? '(likes Tom ?x) 'CxOther)
                 :universe-stored-as-target (stored-as-target? '(admires Tom ?x) 'CxUniverse)
                 :other-reads               (reads? 'CxOther)
                 :universe-reads            (reads? 'CxUniverse)
                 :below-reads               (reads? 'CxBelow)}))))
        (pr-str order))))

(deftest two-rewriteof-targets-mint-the-expression-in-every-order
  ;; CxD sees CxA and CxB (both state Mary) and CxC (states Jane)
  (doseq [order (orders '[CxA CxB CxC])]
    (is (true? (on-own-kb
                (fn [kb]
                  (v/assert kb '(reifiable_function MotherFn) 'CxUniverse)
                  (doseq [c '[CxA CxB CxC CxD]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
                  (doseq [c '[CxA CxB CxC]] (v/assert kb (list 'genlCx 'CxD c) 'CxUniverse))
                  (doseq [c order]
                    (v/assert kb (list 'rewriteOf (if (= 'CxC c) 'Jane 'Mary) '(MotherFn Muffet)) c))
                  (v/assert kb '(likes Tom (MotherFn Muffet)) 'CxD)
                  (let [xs (map #(nth (:sentence %) 2) (v/sentexes-matching kb '(likes Tom ?x) 'CxD))]
                    (and (= 1 (count xs)) (nat-read/reified-nat-symbol? (first xs)))))))
        (pr-str order))))

(defn- rewrite-reads
  "`{:application :target}`, whether `(likes Tom (MotherFn Muffet))` and `(likes Tom
  Mary)` hold in `reader` after `steps`, `[sentence context]` asserted in turn, on a KB of
  its own."
  [steps reader]
  (on-own-kb
   (fn [kb]
     (v/assert kb '(reifiable_function MotherFn) 'CxUniverse)
     (doseq [[s c] steps] (v/assert kb s c))
     {:application (v/ask? kb '(likes Tom (MotherFn Muffet)) reader)
      :target      (v/ask? kb '(likes Tom Mary) reader)})))

(deftest a-compound-rewriteof-reads-the-same-in-every-order-of-rewrite-use-and-edge
  ;; each order against the fresh load, the listed order: one context; CxBelow under
  ;; CxStory by an edge; CxNew under CxUniverse by an edge
  (doseq [[steps reader] '[[[[(rewriteOf Mary (MotherFn Muffet)) CxUniverse]
                             [(likes Tom (MotherFn Muffet)) CxUniverse]] CxUniverse]
                           [[[(genlCx CxBelow CxStory) CxUniverse]
                             [(rewriteOf Mary (MotherFn Muffet)) CxStory]
                             [(likes Tom (MotherFn Muffet)) CxBelow]] CxBelow]
                           [[[(genlCx CxNew CxUniverse) CxUniverse]
                             [(rewriteOf Mary (MotherFn Muffet)) CxUniverse]
                             [(likes Tom (MotherFn Muffet)) CxNew]] CxNew]]
          :let  [fresh (rewrite-reads steps reader)]
          order (orders steps)]
    (is (= {:application true :target true} fresh))
    (is (= fresh (rewrite-reads order reader)) (pr-str order))))

(deftest a-collision-a-merge-joins-in-a-context-is-repaired-there-in-every-order
  ;; `[asked in CxQ, asked in CxQ, asked in CxUniverse, repair equalities in CxQ]`
  (doseq [order (orders [:apple :malus :merge :edge])]
    (is (= [true true false 1]
           (on-own-kb
            (fn [kb]
              (v/assert kb '(reifiable_function FruitFn) 'CxUniverse)
              (doseq [step order]
                (case step
                  :apple (v/assert kb '(color (FruitFn AppleTree) Red) 'CxUniverse)
                  :malus (v/assert kb '(taste (FruitFn MalusTree) Sweet) 'CxUniverse)
                  :merge (v/assert kb '(sameAs AppleTree MalusTree) 'CxQ)
                  :edge  (v/assert kb '(genlCx CxQ CxUniverse) 'CxUniverse)))
              [(v/ask? kb '(taste (FruitFn AppleTree) Sweet) 'CxQ)
               (v/ask? kb '(color (FruitFn MalusTree) Red) 'CxQ)
               (v/ask? kb '(taste (FruitFn AppleTree) Sweet) 'CxUniverse)
               (count (v/sentexes-matching kb '(equals ?x ?y) 'CxQ))])))
        (pr-str order))))

(deftest a-constant-minted-where-a-merge-is-not-visible-is-merged-where-it-is
  (is (= {:ann-pomme true :ann-apple false :universe true}
         (on-own-kb (fn [kb]
                      (v/assert kb '(reifiable_function FruitFn) 'CxUniverse)
                      (v/assert kb '(color (FruitFn Apple) Red) 'CxUniverse)
                      (v/assert kb '(sameAs Apple Pomme) 'CxUniverse)
                      (v/assert kb '(likes Tom (FruitFn Pomme)) 'CxAgentAnn)
                      {:ann-pomme (v/ask? kb '(likes Tom (FruitFn Pomme)) 'CxAgentAnn)
                       :ann-apple (v/ask? kb '(likes Tom (FruitFn Apple)) 'CxAgentAnn)
                       :universe  (v/same-class? kb (nat-read/dedup-constant kb '(FruitFn Apple))
                                                 (nat/constant-for nat-read/nat-namespace '(FruitFn Pomme)))})))))

;; ---- a correspondence stated in one context ---------------------------------

(tu/deftest-kb ^:red a-correspondence-stated-in-one-context-does-not-merge-its-predicates-values-in-another
  ;; A correspondence can hold only under a simplifying theory.  In an atlas where every
  ;; country has one capital, `capitalOf` is functional and `CapitalFn` names its value;
  ;; the world gives one country two.  An application written in the world before its
  ;; values must not be retired onto each value in turn, which equates the two values
  ;; through the placeholder.  Red because the declaration is read KB-wide
  ;; (`res/believed-correspondences`), so the world reads the atlas's correspondence and
  ;; merges the two capitals.
  (tu/with-terms [CapitalFn capitalOf country city locatedIn Bolivia LaPaz Sucre Embassy
                  CxAtlas CxWorld]
    (doseq [s [(list 'genlCx CxAtlas 'CxUniverse) (list 'genlCx CxWorld 'CxUniverse)
               (list 'reifiable_function CapitalFn) (list 'unary_function CapitalFn)
               (list 'arg CapitalFn 1 country) (list 'result CapitalFn city)
               (list 'binary_predicate capitalOf)
               (list 'arg capitalOf 1 country) (list 'arg capitalOf 2 city)
               (list country Bolivia) (list city LaPaz) (list city Sucre)]]
      (v/assert kb s 'CxUniverse))
    (v/assert kb (list 'functionCorrespondingPredicate CapitalFn capitalOf 2) CxAtlas)
    (v/assert kb (list locatedIn Embassy (list CapitalFn Bolivia)) CxWorld)
    (v/assert kb (list capitalOf Bolivia LaPaz) CxAtlas)
    (testing "the atlas reads the correspondence: the application resolves to its value"
      (let [h (v/assert kb (list locatedIn Embassy (list CapitalFn Bolivia)) CxAtlas)]
        (is (= (list locatedIn Embassy LaPaz) (:sentence (v/sentex kb h))))))
    (v/assert kb (list capitalOf Bolivia LaPaz) CxWorld)
    (v/assert kb (list capitalOf Bolivia Sucre) CxWorld)
    (testing "the world does not: its two values stay two, and nothing clashes"
      (is (not (v/same-class? kb LaPaz Sucre CxWorld)))
      (is (= #{LaPaz Sucre} (set (map '?c (v/ask kb (list capitalOf Bolivia '?c) CxWorld)))))
      (is (empty? (v/conflicts kb)))
      (is (empty? (v/contradictions kb))))))

;; ---- the stated position and the binary correspondence ----------------------
;; `functionCorrespondingPredicate` always states the value position.
;; `functionCorrespondingBinaryPredicate` states the common case, a binary predicate with
;; the value second: one core.txt rule concludes the ternary from it, and the engine reads
;; only the ternary.

(tu/deftest-kb a-correspondence-without-a-position-is-refused
  (tu/with-terms [MotherFn motherOf]
    (let [e (try (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse) nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (= :not-well-formed (:type (ex-data e)))))))

(tu/deftest-kb the-shipped-correspondences-state-their-position
  (is (true? (v/ask? kb '(functionCorrespondingBinaryPredicate MotherFn motherOf) 'CxUniverse)))
  (is (true? (v/ask? kb '(functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)))
  (is (true? (v/ask? kb '(functionCorrespondingPredicate QuantityFn measureInUnit 3) 'CxUniverse)))
  (is (true? (v/ask? kb '(functionCorrespondingPredicate InstantFn calendarInstant 7) 'CxUniverse)))
  (is (empty? (filter #(and (= 'functionCorrespondingPredicate (first (:sentence %)))
                            (= 3 (count (:sentence %))))
                      (kb/find-sentexes kb 'functionCorrespondingPredicate)))
      "no correspondence is stored without its position"))

(tu/deftest-kb a-binary-correspondence-puts-the-value-second
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'binary_predicate motherOf) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingBinaryPredicate MotherFn motherOf) 'CxUniverse)
    (is (true? (v/ask? kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse))
        "the rule concludes the ternary")
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)]
      (is (= (list caresFor Bob Mary) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-binary-correspondence-arriving-last-reconciles-what-was-already-minted
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'binary_predicate motherOf) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat-read/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'functionCorrespondingBinaryPredicate MotherFn motherOf) 'CxUniverse)
      (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx)))
      (is (= Mary (nat-read/dedup-constant kb (list MotherFn Muffet)))))))

(tu/deftest-kb a-binary-correspondence-projects-a-placeholder-and-retracting-it-stops-the-read
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'binary_predicate motherOf) 'CxUniverse)
    (let [d (v/assert kb (list 'functionCorrespondingBinaryPredicate MotherFn motherOf) 'CxUniverse)
          h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))
      (v/retract! kb d)
      (is (false? (v/ask? kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)))
      (is (empty? (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))
      (v/retract! kb h))))

(tu/deftest-kb ^:red a-binary-correspondence-respells-a-rule-in-every-order
  ;; Red in the three orders that store the rule before the binary declaration: the
  ;; ternary it concludes is derived, and a derived declaration moves no rule
  ;; (docs/nat.md, What reification does not cover), so the rule keeps its written spelling.
  (doseq [order (orders [:corr :rule :facts])]
    (tu/with-terms [FruitFn AppleTree Gala tagged ripe fruitOf]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (v/assert kb (list 'binary_predicate fruitOf) 'CxUniverse)
      (let [steps {:corr  [(list 'functionCorrespondingBinaryPredicate FruitFn fruitOf)]
                   :rule  [(list 'set/forwardRule
                                 (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t)))]
                   :facts [(list fruitOf AppleTree Gala) (list tagged Gala)]}
            hs    (into {} (map (fn [step] [step (mapv #(v/assert kb % 'CxUniverse) (steps step))])) order)]
        (is (= [{'?t AppleTree}] (v/query kb (list ripe '?t) 'CxUniverse)) (str order))
        (v/retract! kb (first (:corr hs)))
        (is (empty? (v/query kb (list ripe '?t) 'CxUniverse)) (str order " retracted"))
        (run! #(v/retract! kb %) (mapcat val (dissoc hs :corr)))))))

(tu/deftest-kb a-binary-correspondence-types-the-second-argument-by-the-result
  (tu/with-terms [ShadeFn shadeOf paint shade]
    (v/assert kb (list 'reifiable_function ShadeFn) 'CxUniverse)
    (v/assert kb (list 'unary_function ShadeFn) 'CxUniverse)
    (v/assert kb (list 'binary_predicate shadeOf) 'CxUniverse)
    (v/assert kb (list 'arg shadeOf 1 paint) 'CxUniverse)
    (v/assert kb (list 'result ShadeFn shade) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingBinaryPredicate ShadeFn shadeOf) 'CxUniverse)
    (is (true? (v/ask? kb (list 'arg shadeOf 2 shade) 'CxUniverse)))))

(tu/deftest-kb two-positions-for-one-function-and-predicate-collide
  (tu/with-terms [StreetCornerFn streetCornerOf]
    (let [h1 (v/assert kb (list 'functionCorrespondingPredicate StreetCornerFn streetCornerOf 1) 'CxUniverse)
          h2 (v/assert kb (list 'functionCorrespondingPredicate StreetCornerFn streetCornerOf 3) 'CxUniverse)]
      (is (some #(and (= :functional (:kind %)) (= #{h1 h2} (set (:handles %)))) (v/conflicts kb)))
      (is (= :definitional-clash
             (:type (ex-data (try (v/try-assert kb (list 'functionCorrespondingPredicate StreetCornerFn
                                                         streetCornerOf 2)
                                                'CxUniverse)
                                  nil
                                  (catch clojure.lang.ExceptionInfo e e)))))))))

(tu/deftest-kb two-functions-for-one-predicate-and-position-collide
  (tu/with-terms [MotherFn MumFn motherOf]
    (let [h1 (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf 2) 'CxUniverse)
          h2 (v/assert kb (list 'functionCorrespondingPredicate MumFn motherOf 2) 'CxUniverse)]
      (is (some #(and (= :functional (:kind %)) (= #{h1 h2} (set (:handles %)))) (v/conflicts kb))))))
