;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-test
  "Non-atomic terms (NATs) — docs/nat.md.

  A ground reifiable NAT `(FruitFn AppleTree)` reifies to an opaque `nat/` constant
  before it reaches the index (Strategy A), so it autoindexes like an atomic symbol;
  an unreifiable structural NAT `(QuantityFn 5 Kilogram)` stays structural.  The constant↔
  expression map is an ordinary `(natFormula K E)` fact, so rename rides the equality
  migration and remove rides the retraction sweep."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- k-of
  "The reified constant a stored NAT-bearing sentence's arg1 became."
  [kb h] (second (:sentence (v/sentex kb h))))

(defn- fresh-constant
  "A reified constant named by gensym rather than by content, `nat/g…`: a second
  constant for one expression, as a `:bulk?` load or an import can store."
  [] (symbol nat/nat-namespace (name (gensym "g"))))

;; ---- 1. round-trip -------------------------------------------------------

(tu/deftest-kb round-trip-stores-an-opaque-constant
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (testing "the stored sentence holds an opaque constant, not the compound"
        (is (nat/reified-nat-symbol? k))
        (is (= (list 'color k 'Red) (:sentence (v/sentex kb h))))
        (is (not-any? sequential? (rest (:sentence (v/sentex kb h))))))
      (testing "the materialized result type holds"
        (is (seq (v/sentexes-matching kb (list fruit k) '?ctx))))
      (testing "a NAT-bearing query resolves to the stored constant"
        (is (= [{'?c 'Red}] (v/ask kb (list 'color (list FruitFn AppleTree) '?c) 'CxUniverse))))
      (testing "display expands the constant back to its functional expression"
        (is (= (list 'color (list FruitFn AppleTree) 'Red)
               (nat/expand-expression kb (:sentence (v/sentex kb h))))))
      (testing "an unknown NAT resolves to no-match and mints nothing"
        (let [before (count (v/sentexes-matching kb (list 'natFormula '?k '?e) 'CxUniverse))]
          (is (empty? (v/sentexes-matching kb (list 'color (list FruitFn 'PearTree) '?c) '?ctx)))
          (is (= before (count (v/sentexes-matching kb (list 'natFormula '?k '?e) 'CxUniverse)))))))))

(tu/deftest-kb handle-of-and-why-not-resolve-a-nat-to-its-stored-constant
  ;; `ist` stores the constant, so its non-creating counterpart has to ask for the
  ;; constant: a lookup of the compound as written answered nil while `sentexes-matching`
  ;; and `ask?` found the sentex, and the documented composition
  ;; `(retract! kb (handle-of kb s c))` was a silent no-op.
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
  ;; `assert-inert` reifies for read (dedup, never mint): a NAT with a stored constant is
  ;; stored under it — where a later `assert` dedups to the one record instead of minting a
  ;; twin, and every belief-blind read finds it from the compound spelling.  Stored raw the
  ;; compound was a record `sentexes-matching`/`ask` reified past, `count-with-functor`
  ;; answered 2 for one proposition, and the reads split across two spellings.  A NAT this
  ;; KB never minted is refused (`:unminted-nat`): minting a `natFormula` is the belief-
  ;; carrying side effect this entry point never has.
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
  ;; `canonical-sentex` claims "the exact form `assert` would key on"; `assert` keys a NAT
  ;; sentence on the minted constant, so this reifies for read (dedup, never mint) and
  ;; agrees with `handle-of` and the stored spelling.  A NAT this KB never minted has no
  ;; canonical stored form yet, so the compound is returned unchanged.
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
  ;; Dedup's cross-process twin, and the point of naming by content.  A reified constant is
  ;; named from its expression (`nat/content-name`), not a process-local gensym, so the same
  ;; NAT reifies to the same constant in a KB that has never seen the other — which is what
  ;; lets two dumps merge, and a re-mint after a sweep dedup, rather than collide on two
  ;; names for one expression — a collision `merge-colliding-nats!` reconciles and content
  ;; naming avoids.
  ;; `kb` and a second KB on its own memory store stand in for two processes; the
  ;; process-wide symbol pool interns identity, never equality, so `=` is the test that
  ;; holds across processes.
  (tu/with-terms [FruitFn AppleTree]
    (let [mint! (fn [k]
                  (v/assert k (list 'reifiable_function FruitFn) 'CxUniverse)
                  (k-of k (v/assert k (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)))
          open! #(v/open-kb {:backend :memory :space (gensym "nat-determinism")})
          a     (open!)
          b     (open!)
          [k1 k2] (try [(mint! a) (mint! b)]
                       (finally (v/close! a) (v/close! b)))]
      (is (nat/reified-nat-symbol? k1) "a nat/ constant, not the raw compound")
      (is (= k1 k2)
          "the same expression, the same content-named constant, in two independent KBs"))))

(tu/deftest-kb a-vector-spelled-nat-is-the-nat-the-list-spelling-names
  ;; Reification runs **before** `canon`, and canon makes `[F a]` and `(F a)` one
  ;; sentence — so a gate on the list spelling alone stores the raw compound for one
  ;; spelling and the constant for the other: two handles and two maps for one claim,
  ;; decided by how whoever typed it spelled a bracket.  Both arrival orders, since the
  ;; second spelling has to resolve to what the first stored either way round.
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
        (is (nat/reified-nat-symbol? (nth (:sentence (v/sentex kb ha)) 2))
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
          inner-k  (nat/dedup-constant kb (list BestTreeIn Orchard1))
          outer-k  (k-of kb h)]
      (testing "both the inner and outer NAT have a natFormula"
        (is (nat/reified-nat-symbol? inner-k))
        (is (nat/reified-nat-symbol? outer-k))
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
        (is (= k (nat/dedup-constant kb (list FruitFn MalusTree))))
        (is (= 1 (count (v/sentexes-matching kb (list 'natFormula '?k (list FruitFn MalusTree))
                                             'CxUniverse)))))
      (testing "the retired spelling stays a usable question, resolving to the same K"
        ;; AppleTree is deprecated to MalusTree, so a goal naming the old term rewrites
        ;; to the new expression before lookup (docs/equality.md) and still finds K
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))))))

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
          (is (= survivor (nat/dedup-constant kb (list FruitFn MalusTree)))
              "the lexicographically smallest constant survives"))))))

(tu/deftest-kb a-collision-resolves-to-the-constant-the-repair-would-keep
  ;; Two constants can name one expression without a rename: a `:bulk?` load skips the
  ;; dedup probe and an import restores whatever the dump held, and neither is swept up
  ;; by the next unrelated equality.  `group-collisions` elects the lexicographically
  ;; smallest as the survivor a merge keeps, so the *read* has to answer with that one —
  ;; answering with whichever the retrieval yielded first makes the expression denote a
  ;; different term in a KB whose two maps arrived the other way round, and every later
  ;; read inherits it.  So both orders, and one answer.
  (doseq [smallest-first? [true false]]
    (tu/with-terms [FruitFn AppleTree]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (let [E     (list FruitFn AppleTree)
            ks    (vec (sort [(fresh-constant) (fresh-constant)]))
            what  (str "the " (if smallest-first? "smallest" "largest") " asserted first")]
        ;; staged the way the mint writes one — the map is `:monotonic` bookkeeping,
        ;; and the second is the one no dedup probe stopped
        (doseq [k (if smallest-first? ks (rseq ks))]
          (v/assert kb (list 'natFormula k E) 'CxUniverse {:strength :monotonic}))
        (is (= 2 (count (v/sentexes-matching kb (list 'natFormula '?k E) 'CxUniverse)))
            (str what ": both maps stand, so there is a collision to resolve"))
        (is (= (first ks) (nat/dedup-constant kb E)) what)
        (is (= [(first ks)]
               (vec (keep (fn [[survivor dups]]
                            (when (= (set ks) (set (cons survivor dups))) survivor))
                          (nat/colliding-constant-groups kb))))
            (str what ": and the read named the survivor the repair elects"))))))

(tu/deftest-kb one-constant-mapped-to-two-expressions-is-swept-against-one-of-them
  ;; The collision running the other way: one constant, two expressions, the 1:1 invariant
  ;; not yet restored.  Two readers consult that map and they have to agree — `orphan?`
  ;; decides whether `k` is collectable, and `bookkeeping-handles` computes what the sweep
  ;; then retracts.  Reading it two different ways lets the sweep call `k` orphaned on
  ;; expression E₁ and retract the bookkeeping it computed for E₂: a materialized type of
  ;; the *other* expression is left stored, naming a constant that has been collected.
  ;;
  ;; Both readers take the **content-least** expression, so the answer is one whichever
  ;; order the two maps arrived in — which is what the two arms below compare.  Each arm
  ;; stores one materialized result type, once belonging to the authoritative expression's
  ;; function and once to the other's, since that is what makes the two verdicts differ.
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
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb removing-the-last-rule-naming-a-reified-nat-collects-it
  (tu/with-terms [FruitFn AppleTree fruit likes knows]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'implies (list likes '?x (list FruitFn AppleTree))
                               (list knows '?x AppleTree))
                      'CxUniverse)]
      (is (some? (nat/dedup-constant kb (list FruitFn AppleTree)))
          "the rule's antecedent reified the NAT")
      (v/retract! kb h)
      (testing "the teardown reads a rule's antecedent as a use, so the constant goes with it"
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

;; The sweep separates a use from bookkeeping by **what the mint wrote**, not by what a
;; sentence looks like.  The two are not the same question: a user's own unary claim about
;; a reified NAT has a materialized result type's shape — `(T K)`, and `(genl K T)` for the
;; subtype half — so a sweep reading shape retracts the claim along with the constant, in
;; silence and with nothing to read afterwards that says it happened.

(tu/deftest-kb a-users-unary-claim-about-a-reified-nat-is-a-use-not-bookkeeping
  (tu/with-terms [FruitFn AppleTree prime noted Author]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h  (v/assert kb (list noted Author (list FruitFn AppleTree)) 'CxUniverse)
          k  (nth (:sentence (v/sentex kb h)) 2)
          hu (v/assert kb (list prime (list FruitFn AppleTree)) 'CxUniverse)]
      (testing "both facts stand on one constant, and neither is a declared result type"
        (is (nat/reified-nat-symbol? k))
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
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

;; A use is counted by **storage**, and the two tests below are the two ways a stored use
;; is not a believed one.  Either way the constant has to stay: a sentence naming it is in
;; the store, so collecting the map would leave that sentence holding a raw `nat/` symbol
;; nothing maps — and re-reifying the expression would then mint a second constant beside
;; the first, a collision no merge repair caused.

(tu/deftest-kb a-defeated-use-keeps-the-constant-until-it-is-actually-removed
  ;; The claim is defeated by the constant's own materialized result type, which is
  ;; `:monotonic` bookkeeping — so nothing a *use* could be read off has moved, and the
  ;; claim sits in the store exactly where a relabel can give it back.  Which is what
  ;; happens two lines later.
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
          (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))
          (is (= hs (v/handle-of kb (list stone_t k) 'CxUniverse))))
        (v/retract! kb hd)
        (testing "and the defeat lifting revives a use naming a constant still mapped"
          (is (true? (v/in? kb hs)))
          (is (= (list FruitFn AppleTree) (nat/nat-expression kb k))))
        (v/retract! kb hs)
        (testing "removing it is what makes the constant an orphan, and it is collected"
          (is (empty? (kb/find-sentexes kb k)))
          (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
          (is (empty? (nat/orphaned-constants kb))))))))

(tu/deftest-kb an-inert-use-keeps-the-constant-though-it-has-no-node-at-all
  ;; The other half, and the one belief cannot speak about either way: an inert sentex —
  ;; a labeling's materialized truth value — is never a premise, so it has no TMS node to
  ;; be IN or OUT.  It still names the constant, and it is still in the store.
  (tu/with-terms [FruitFn AppleTree noted Author color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)
          i (v/assert-inert kb (list noted Author k) 'CxUniverse)]
      (is (nat/reified-nat-symbol? k))
      (is (false? (v/in? kb i)) "inert: stored, and never believed")
      (v/retract! kb h)
      (testing "the believed use went and the inert one holds the constant"
        (is (false? (nat/orphan? kb k)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree)))))
      (v/retract! kb i)
      (testing "and once that goes too the sweep collects — no dangling nat/ symbol"
        (is (empty? (kb/find-sentexes kb k)))
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
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
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb the-bookkeeping-set-is-an-answer-rather-than-a-plan
  ;; The caller retracts what `bookkeeping-handles` hands back, and the question
  ;; "is this one of `k`'s own?" is itself read off `k`'s `natFormula` — so an answer
  ;; still being computed while the caller acts on it reads a KB the caller has already
  ;; torn the map out of, and everything after that point stops looking like
  ;; bookkeeping.  What survives is a materialized type naming a collected constant.
  ;; The order the term index yields decides whether it happens, so the two tests above
  ;; witness it only in some retrieval orders; this one pins the property instead.
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

;; The sweep asks about the constants the teardown's removals named, so a nested NAT —
;; whose only reference is the expression the *outer* constant's map holds — is reached
;; only on the round after the outer one goes.  Its collection is what says the region
;; grows with the fixpoint rather than being fixed at the seed.

(tu/deftest-kb collecting-an-orphan-cascades-to-the-nat-nested-in-its-expression
  (tu/with-terms [FruitFn BestTreeIn Orchard1]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'reifiable_function BestTreeIn) 'CxUniverse)
    (let [h       (v/assert kb (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
                            'CxUniverse)
          outer-k (k-of kb h)
          inner-k (nat/dedup-constant kb (list BestTreeIn Orchard1))]
      (testing "the inner constant is referenced only by the outer one's expression"
        (is (nat/reified-nat-symbol? inner-k))
        (is (= (list FruitFn inner-k) (nat/nat-expression kb outer-k)))
        (is (false? (nat/orphan? kb inner-k))))
      (v/retract! kb h)
      (testing "the outer constant goes with its last use"
        (is (empty? (kb/find-sentexes kb outer-k)))
        (is (nil? (nat/dedup-constant kb (list FruitFn inner-k)))))
      (testing "and the inner one goes with the expression that was naming it"
        (is (empty? (kb/find-sentexes kb inner-k)))
        (is (nil? (nat/dedup-constant kb (list BestTreeIn Orchard1)))))
      (is (empty? (nat/orphaned-constants kb))))))

;; A use does not always leave by the retraction's own dependency sweep: an exception
;; that starts holding blocks a justification, and the settle that follows deletes what
;; it was solely supporting (docs/exceptions.md).  Nothing is retracted here at all, so
;; the constant is reachable only through what the *settle* removed.

(tu/deftest-kb a-nat-whose-use-the-settle-swept-is-collected-too
  (tu/with-terms [FruitFn AppleTree fruity brightAs weather overcast Sunny Sun]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    ;; `fruity` is the function's declared result type, so the sentence that mints the
    ;; constant is the constant's own materialized type — one sentex, and bookkeeping.
    ;; The exception is about the weather rather than about the fruit, so the rule's
    ;; conclusion is the only sentence in the whole test that names the constant.
    (v/assert kb (list 'result FruitFn fruity) 'CxUniverse)
    (let [h (v/assert kb (list fruity (list FruitFn AppleTree)) 'CxUniverse)
          k (k-of kb h)]
      (v/assert kb (list weather Sunny) 'CxUniverse)
      (v/assert kb (list 'exceptWhen (list overcast '?w)
                         (list 'set/defaultRule
                               (list 'set/forwardRule (list 'implies (list 'and (list fruity '?x) (list weather '?w))
                                                            (list brightAs '?x Sun)))))
                'CxUniverse)
      (testing "the rule's conclusion is the constant's one live use"
        (is (nat/reified-nat-symbol? k))
        (is (seq (v/sentexes-matching kb (list brightAs k Sun) 'CxUniverse)))
        (is (false? (nat/orphan? kb k))))
      ;; known-true, so the block sweeps: a `:default` blocker stores the conclusion with a
      ;; defeat, and the constant keeps that use
      (v/edit! kb {:add [[(list overcast Sunny) 'CxUniverse {:strength :monotonic}]]})
      (testing "the exception blocks the rule and the settle sweeps the conclusion"
        (is (empty? (v/sentexes-matching kb (list brightAs k Sun) 'CxUniverse))))
      (testing "and the constant it was the last use of goes with it"
        (is (nil? (nat/nat-expression kb k)))
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

;; ---- 6. unreifiable gate -------------------------------------------------

(tu/deftest-kb an-unreifiable-nat-stays-structural
  (tu/with-terms [QuantityFn Obj]
    (v/assert kb (list 'unreifiable_function QuantityFn) 'CxUniverse)
    (let [nut (list QuantityFn 5 'Kilogram)
          h   (v/assert kb (list 'mass Obj nut) 'CxUniverse)]
      (testing "the compound is stored structurally, not minted"
        (is (= (list 'mass Obj nut) (:sentence (v/sentex kb h))))
        (is (nil? (nat/dedup-constant kb nut))))
      (testing "it round-trips unchanged"
        (is (seq (v/sentexes-matching kb (list 'mass Obj nut) '?ctx)))))))

;; ---- 7. no-op cost -------------------------------------------------------

(deftest with-no-reifiable-function-the-reify-pass-is-a-no-op
  ;; life.txt declares FatherFn reifiable, so the KB here is an empty one of its own.
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (tu/with-terms [FruitFn AppleTree]
      (testing "the gate is off and a plain compound is stored verbatim"
        (is (false? (nat/any-reifiable-functions? kb)))
        ;; a compound argument with no reifiable_function declared is left structural
        (let [h (v/assert kb (list 'grows (list FruitFn AppleTree) 'Spring) 'CxUniverse)]
          (is (= (list 'grows (list FruitFn AppleTree) 'Spring) (:sentence (v/sentex kb h)))))))))

;; ---- 8. every read path asks the same question ---------------------------
;;
;; A NAT reifies on the *write* path, so every read path has to reify its goal to meet
;; the stored constant.  `quasiquote/prepare-goal-for-read` is that step, and the interesting
;; failure is not a wrong answer but a **silently empty** one: a path that skips it
;; matches the compound against a store that holds a symbol and finds nothing, which
;; reads exactly like a KB that was never told.  So the claim is parity, checked path
;; by path rather than inferred from the one that works.

(tu/deftest-kb every-read-path-reifies-the-nat-in-its-goal
  (tu/with-terms [CapitalOfFn France isCapital Yes]
    (v/assert kb (list 'reifiable_function CapitalOfFn) 'CxUniverse)
    (let [h (v/assert kb (list isCapital (list CapitalOfFn France) Yes) 'CxUniverse)]
      (testing "the store holds a constant, so a goal spelled as the NAT must be reified"
        (is (nat/reified-nat-symbol? (second (:sentence (v/sentex kb h)))))))
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
  ;; The write walk descends a rule's antecedents, so an `(unknown <NAT goal>)` reifies
  ;; along with the rule around it.  An `exceptWhen`'s conjuncts arrive as a **vector**,
  ;; which is a list of forms rather than a literal — and there the empty answer is not
  ;; merely a missing result.  An exception that cannot be answered does not hold
  ;; (docs/exceptions.md, the open-world reading), so the rule fires unguarded and
  ;; nothing says so.  One evaluator, so all three chainers or none.
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
        (is (nat/reified-nat-symbol? k))
        (is (v/genl? kb k super))))))

(tu/deftest-kb result-arg-types-an-application-that-is-never-minted
  (tu/with-terms [PickFn needsKind kind other Ann]
    (v/assert kb (list 'unreifiable_function PickFn) 'CxUniverse)
    (v/assert kb (list 'resultArg PickFn 1) 'CxUniverse)
    (v/assert kb (list 'genl kind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl other 'thing) 'CxUniverse)
    (v/assert kb (list 'arg needsKind 2 kind) 'CxUniverse)
    (is (some? (v/assert kb (list needsKind Ann (list PickFn kind)) 'CxUniverse))
        "an application naming the demanded type is admitted")
    (is (= :arg-type
           (try (v/assert kb (list needsKind Ann (list PickFn other)) 'CxUniverse) nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
        "and one naming a type outside it is refused")))

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
  ;; `rewrite-target` answers only a **unique** believed declaration, as
  ;; `correspondence-of` answers its twin question: picking between two by whichever
  ;; the retrieval yielded first would store `(likes Tom Mary)` or `(likes Tom
  ;; Maria)` according to arrival order — divergent stored state, inherited by every
  ;; later read.  Two declarations are a disagreement, not a tie to break.
  (tu/with-terms [MotherFn Muffet Mary Maria]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf Mary (list MotherFn Muffet)) 'CxUniverse)
    (v/assert kb (list 'rewriteOf Maria (list MotherFn Muffet)) 'CxUniverse)
    (let [h      (v/assert kb (list 'likes 'Tom (list MotherFn Muffet)) 'CxUniverse)
          stored (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? stored)
          "a fresh constant stands until the disagreement is resolved")
      (is (not (contains? #{Mary Maria} stored))))))

;; ---- recover: the reifiable gate + reified NAT data survive a rebuild -----------

(tu/deftest-kb nat-data-survives-recover
  ;; the reifiable prop and the natFormula / result-type facts are all durable, so a
  ;; rebuild from the records must reconstruct the gate, dedup, and expansion — else a
  ;; recovered KB would disagree with the running one about what a NAT reifies to.
  ;; `recover` rebuilds the taxonomy + JTMS in place from the store (it adds no
  ;; sentex), so the fixture's net-neutral teardown still restores the baseline.
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (v/recover kb)
      (testing "the gate, the constant map, and the materialized type all rebuild"
        (is (true? (nat/any-reifiable-functions? kb)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (seq (v/sentexes-matching kb (list fruit k) '?ctx))))
      (testing "a fresh NAT still dedups to the same constant after recovery"
        (let [h2 (v/assert kb (list 'taste (list FruitFn AppleTree) 'Sweet) 'CxUniverse)]
          (is (= k (k-of kb h2))))))))

;; ---- the corresponding predicate -----------------------------------------
;;
;; `(functionCorrespondingPredicate F P N)` says the function and the predicate state
;; one relationship, so the reify reads it **both** ways: an application resolves to
;; the value `P` already names, and a constant minted for want of one is projected
;; back onto `P`.  What the tests below are really about is the boundary between those
;; two — whichever of the application, the fact and the declaration lands last, the KB
;; ends up holding one term for one application.

(tu/deftest-kb a-corresponding-fact-names-the-term-an-application-reifies-to
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
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
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "no value is known, so the expression mints a placeholder"
        (is (nat/reified-nat-symbol? k)))
      (testing "and the placeholder is projected onto the corresponding predicate"
        (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))))))

(tu/deftest-kb a-value-arriving-after-the-mint-retires-the-placeholder
  ;; the order-independence case.  The fact and the application say the same thing, so
  ;; whichever lands second must not leave the KB with two values for one application.
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
      (testing "one value, and it is the one somebody named"
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse))))
      (testing "the use of the placeholder migrated onto it"
        (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx))))
      (testing "and the expression still resolves — to the real term now"
        (is (= Mary (nat/dedup-constant kb (list MotherFn Muffet))))
        (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))))))

(tu/deftest-kb a-declared-position-puts-the-value-where-it-says
  ;; Cyc's own example: (StreetCornerFn XING DIRECTION) = LOT exactly when
  ;; (streetCornerOf LOT XING DIRECTION), so the value is argument 1 and not the last.
  (tu/with-terms [StreetCornerFn streetCornerOf Xing1 North Lot7 ownedBy Alice]
    (v/assert kb (list 'reifiable_function StreetCornerFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate StreetCornerFn streetCornerOf 1)
              'CxUniverse)
    (v/assert kb (list streetCornerOf Lot7 Xing1 North) 'CxUniverse)
    (let [h (v/assert kb (list ownedBy (list StreetCornerFn Xing1 North) Alice) 'CxUniverse)]
      (is (= (list ownedBy Lot7 Alice) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-declaration-arriving-last-reconciles-what-was-already-minted
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
      (testing "before the declaration the two terms are unrelated"
        (is (= k (nat/dedup-constant kb (list MotherFn Muffet)))))
      (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
      (testing "declaring it last reaches the state declaring it first would have"
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx)))
        (is (= Mary (nat/dedup-constant kb (list MotherFn Muffet))))))))

(tu/deftest-kb a-declaration-arriving-last-projects-a-placeholder-that-has-no-value
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (empty? (v/ask kb (list motherOf Muffet '?m) '?ctx)))
      (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
      (testing "the constant minted before the declaration is projected by it"
        (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))))))

(tu/deftest-kb two-declarations-for-one-function-decide-nothing
  ;; Two correspondences are two different claims about what `(F a…)` denotes.  Choosing
  ;; between them would have to key on a handle, which is the one thing belief may never
  ;; do — so neither is read, and the application mints as if none were declared.
  (tu/with-terms [MotherFn motherOf parentOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn parentOf) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (is (not= Mary k))
      (testing "and neither predicate is projected onto"
        (is (empty? (v/ask kb (list parentOf Muffet '?m) '?ctx)))
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))))))

(tu/deftest-kb retracting-the-declaration-stops-the-application-resolving
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor sees]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [d (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)]
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
      (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))
      (v/retract! kb d)
      (testing "the declaration is belief-following, so the reify stops reading it"
        (is (nil? (nat/correspondence-value kb (list MotherFn Muffet))))
        (let [h (v/assert kb (list sees Bob (list MotherFn Muffet)) 'CxUniverse)]
          (is (nat/reified-nat-symbol? (nth (:sentence (v/sentex kb h)) 2))))))))

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
              (list 'functionCorrespondingPredicate MotherFn Mary)]
             ["a position that is not a positive integer" :not-well-formed
              (list 'functionCorrespondingPredicate MotherFn motherOf 'first)]]]
      (let [e (try (v/assert kb s 'CxUniverse) nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) what)
        (is (= expected (:type (ex-data e))) what)))))

(tu/deftest-kb a-correspondence-survives-recover
  ;; the declaration is read through the index rather than a taxonomy cache, so a
  ;; rebuild has nothing to reconstruct — which is the claim worth pinning, since a
  ;; recovered KB that stopped resolving applications would be a restart changing an
  ;; answer.
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
    (v/recover kb)
    (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)]
      (is (= (list caresFor Bob Mary) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-projection-does-not-keep-an-orphaned-placeholder-alive
  ;; the projection states what the constant *is*, so it is bookkeeping like a result
  ;; type — a constant whose only remaining sentex is its own projection has no live
  ;; use, and treating one as a use would make every placeholder immortal.
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (seq (v/ask kb (list motherOf Muffet '?m) '?ctx)))
      (v/retract! kb h)
      (testing "the placeholder, its map and its projection all go"
        (is (nil? (nat/dedup-constant kb (list MotherFn Muffet))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (v/ask kb (list motherOf Muffet '?m) '?ctx)))
        (is (empty? (nat/orphaned-constants kb)))))))

;; ---- the result type reaches the corresponding predicate -----------------
;; A function's result type is the type of the value its corresponding predicate holds at
;; the value position, so `result` and the correspondence together type that argument of
;; the predicate.  The vocabulary below is made up, so the tests read the rules and no
;; shipped function.

(tu/deftest-kb a-correspondence-types-the-last-argument-of-a-binary-predicate-by-the-result
  (tu/with-terms [GlowFn glowOf lamp glow_level]
    (v/assert kb (list 'reifiable_function GlowFn) 'CxUniverse)
    (v/assert kb (list 'unary_function GlowFn) 'CxUniverse)
    (v/assert kb (list 'binary_predicate glowOf) 'CxUniverse)
    (v/assert kb (list 'arg glowOf 1 lamp) 'CxUniverse)
    (v/assert kb (list 'result GlowFn glow_level) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate GlowFn glowOf) 'CxUniverse)
    (is (true? (v/ask? kb (list 'arg2 glowOf glow_level) 'CxUniverse)))
    (is (false? (v/ask? kb (list 'arg1 glowOf glow_level) 'CxUniverse)))))

(tu/deftest-kb a-correspondence-types-the-last-argument-of-a-ternary-predicate-by-the-result
  (tu/with-terms [BlendFn blendOf paint blend_shade]
    (v/assert kb (list 'reifiable_function BlendFn) 'CxUniverse)
    (v/assert kb (list 'binary_function BlendFn) 'CxUniverse)
    (v/assert kb (list 'ternary_predicate blendOf) 'CxUniverse)
    (v/assert kb (list 'arg blendOf 1 paint) 'CxUniverse)
    (v/assert kb (list 'arg blendOf 2 paint) 'CxUniverse)
    (v/assert kb (list 'result BlendFn blend_shade) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate BlendFn blendOf) 'CxUniverse)
    (is (true? (v/ask? kb (list 'arg3 blendOf blend_shade) 'CxUniverse)))
    (is (false? (v/ask? kb (list 'arg2 blendOf blend_shade) 'CxUniverse)))))

(tu/deftest-kb a-correspondence-types-the-last-argument-of-a-quaternary-predicate-by-the-result
  (tu/with-terms [MixFn mixOf paint mix_shade]
    (v/assert kb (list 'reifiable_function MixFn) 'CxUniverse)
    (v/assert kb (list 'ternary_function MixFn) 'CxUniverse)
    (v/assert kb (list 'quaternary_predicate mixOf) 'CxUniverse)
    (doseq [position [1 2 3]]
      (v/assert kb (list 'arg mixOf position paint) 'CxUniverse))
    (v/assert kb (list 'result MixFn mix_shade) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MixFn mixOf) 'CxUniverse)
    (is (true? (v/ask? kb (list 'arg mixOf 4 mix_shade) 'CxUniverse)))
    (is (false? (v/ask? kb (list 'arg mixOf 3 mix_shade) 'CxUniverse)))))

(tu/deftest-kb a-correspondence-types-the-last-argument-of-a-quinary-predicate-by-the-result
  (tu/with-terms [PaletteFn paletteOf paint palette_shade]
    (v/assert kb (list 'reifiable_function PaletteFn) 'CxUniverse)
    (v/assert kb (list 'quaternary_function PaletteFn) 'CxUniverse)
    (v/assert kb (list 'quinary_predicate paletteOf) 'CxUniverse)
    (doseq [position [1 2 3 4]]
      (v/assert kb (list 'arg paletteOf position paint) 'CxUniverse))
    (v/assert kb (list 'result PaletteFn palette_shade) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate PaletteFn paletteOf) 'CxUniverse)
    (is (true? (v/ask? kb (list 'arg paletteOf 5 palette_shade) 'CxUniverse)))
    (is (false? (v/ask? kb (list 'arg paletteOf 4 palette_shade) 'CxUniverse)))))

(tu/deftest-kb a-ternary-correspondence-types-the-argument-at-its-declared-position-by-the-result
  (tu/with-terms [CornerFn cornerOf crossing heading corner_lot]
    (v/assert kb (list 'reifiable_function CornerFn) 'CxUniverse)
    (v/assert kb (list 'binary_function CornerFn) 'CxUniverse)
    (v/assert kb (list 'ternary_predicate cornerOf) 'CxUniverse)
    (v/assert kb (list 'arg cornerOf 2 crossing) 'CxUniverse)
    (v/assert kb (list 'arg cornerOf 3 heading) 'CxUniverse)
    (v/assert kb (list 'result CornerFn corner_lot) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate CornerFn cornerOf 1) 'CxUniverse)
    (is (true? (v/ask? kb (list 'arg1 cornerOf corner_lot) 'CxUniverse)))
    (is (false? (v/ask? kb (list 'arg3 cornerOf corner_lot) 'CxUniverse)))))

;; ---- the derivation path -------------------------------------------------
;; A forward rule whose consequent builds a function term stores what `assert` stores:
;; the application's constant, never the compound.  Both write paths agree on what one
;; term is, so a derived sentence and an asserted one about the same application meet
;; in a join, answer a goal spelled with the compound, and carry the result type.

(defn- orchard-rules!
  "The rule that derives an application, and the rule that joins it with an asserted
  claim about the same application."
  [kb FruitFn bears grownIn tagged picked]
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
  (tu/with-terms [FruitFn AppleTree Orchard fruit bears grownIn tagged picked]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [derive! #(do (orchard-rules! kb FruitFn bears grownIn tagged picked)
                       (v/assert kb (list bears AppleTree Orchard) 'CxUniverse))
          claim!  #(v/assert kb (list tagged (list FruitFn AppleTree)) 'CxUniverse)
          _       (if (= order :derived-first) (do (derive!) (claim!)) (do (claim!) (derive!)))
          k       (nat/dedup-constant kb (list FruitFn AppleTree))]
      (testing (str order ": the derived sentence holds the constant, not the compound")
        (is (nat/reified-nat-symbol? k))
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
  (tu/with-terms [FruitFn AppleTree Orchard fruit bears grownIn tagged picked]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (orchard-rules! kb FruitFn bears grownIn tagged picked)
    (let [hb (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)
          ht (v/assert kb (list tagged (list FruitFn AppleTree)) 'CxUniverse)
          k  (nat/dedup-constant kb (list FruitFn AppleTree))
          [first-h second-h] (if (= order :derived) [hb ht] [ht hb])]
      (is (nat/reified-nat-symbol? k))
      (v/retract! kb first-h)
      (testing (str order ": the remaining use keeps the constant")
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (false? (nat/orphan? kb k)))
        (is (not (v/ask? kb (list picked Orchard) 'CxUniverse)) "the join lost one side"))
      (when (= order :derived)
        (testing "retracting the antecedent withdraws the derived fact"
          (is (empty? (v/sentexes-matching kb (list grownIn '?f Orchard) 'CxUniverse)))))
      (v/retract! kb second-h)
      (testing (str order ": the last use going collects the constant and its bookkeeping")
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb withdrawing-the-derived-use-collects-the-constant-in-either-order
  (withdrawal-collects-the-constant kb :derived)
  (withdrawal-collects-the-constant kb :asserted))

(tu/deftest-kb a-constant-minted-by-a-firing-is-collected-and-re-minted-under-its-name
  (tu/with-terms [FruitFn AppleTree Orchard fruit bears grownIn tagged picked]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (orchard-rules! kb FruitFn bears grownIn tagged picked)
    (let [h (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)
          k (nat/dedup-constant kb (list FruitFn AppleTree))]
      (testing "the firing alone mints the constant"
        (is (nat/reified-nat-symbol? k))
        (is (v/ask? kb (list grownIn k Orchard) 'CxUniverse)))
      (v/retract! kb h)
      (testing "the derived use was the only one, so the constant goes with it"
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb))))
      (let [h2 (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)]
        (testing "re-deriving mints the same constant, since the name is the expression's"
          (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))
          (is (v/ask? kb (list grownIn k Orchard) 'CxUniverse)))
        (v/retract! kb h2)))))

(tu/deftest-kb a-stamped-rule-names-the-constant-in-its-antecedent
  ;; a generator's stamped rule is a derived conclusion too, and a ground application in
  ;; its antecedent has to be the constant the stored claim is spelled with, or the
  ;; stamped rule never matches the claim
  (tu/with-terms [FruitFn AppleTree marked tagged ripe]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list tagged (list FruitFn AppleTree)) 'CxUniverse)
    (v/assert kb (list 'implies (list marked '?t)
                       (list 'set/forwardRule
                             (list 'implies (list tagged (list FruitFn '?t)) (list ripe '?t))))
              'CxUniverse)
    (v/assert kb (list marked AppleTree) 'CxUniverse)
    (is (v/ask? kb (list ripe AppleTree) 'CxUniverse))))

(tu/deftest-kb a-conclusion-the-checks-drop-mints-no-constant
  ;; the placement's checks read the application before the mint, so a conclusion they
  ;; drop leaves no constant whose one use was never stored
  (tu/with-terms [FruitFn AppleTree Orchard fruit beast bears grownIn]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'genl fruit 'thing) 'CxUniverse)
    (v/assert kb (list 'genl beast 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint fruit beast) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (v/assert kb (list 'arg grownIn 1 beast) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list bears '?t '?o) (list grownIn (list FruitFn '?t) '?o)))
              'CxUniverse)
    (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)
    (is (empty? (v/sentexes-matching kb (list grownIn '?f Orchard) 'CxUniverse))
        "the conclusion is dropped")
    (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))) "and nothing was minted for it")
    (is (some #(= grownIn (first (:sentence %))) (v/violations kb))
        "the drop is recorded")))

(tu/deftest-kb a-mint-the-assert-path-refuses-drops-the-conclusion-without-throwing
  ;; the correspondence projects the new constant onto a predicate whose `arg` declaration
  ;; its result type is disjoint from, so the mint's own assert refuses; a firing may not
  ;; throw, so the conclusion is dropped and the refusal recorded.  Pinned to the
  ;; constraint reading, where the declaration convicts the constant; the entailing one
  ;; mints `(beast …)` beside `(fruit …)` and stores the clash (docs/argtypes.md)
  (tu/without-entailing
   (tu/with-terms [FruitFn AppleTree Pear Orchard fruit beast keeperOf bears grownIn tagged]
     (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
     (v/assert kb (list 'genl fruit 'thing) 'CxUniverse)
     (v/assert kb (list 'genl beast 'thing) 'CxUniverse)
     (v/assert kb (list 'disjoint fruit beast) 'CxUniverse)
     (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
     (v/assert kb (list 'arg keeperOf 2 beast) 'CxUniverse)
     (v/assert kb (list 'functionCorrespondingPredicate FruitFn keeperOf) 'CxUniverse)
     (testing "the assert path refuses the same application"
       (is (thrown? clojure.lang.ExceptionInfo
                    (v/assert kb (list tagged (list FruitFn Pear)) 'CxUniverse))))
     (v/assert kb (list 'set/forwardRule
                        (list 'implies (list bears '?t '?o) (list grownIn (list FruitFn '?t) '?o)))
               'CxUniverse)
     (is (some? (v/assert kb (list bears AppleTree Orchard) 'CxUniverse))
         "the assert that fires the rule is not refused")
     (is (empty? (v/sentexes-matching kb (list grownIn '?f Orchard) 'CxUniverse))
         "the conclusion is dropped")
     (is (some #(and (= :mint-refused (:violation %)) (= grownIn (first (:sentence %)))
                     (keyword? (get-in % [:detail :refusal])))
               (v/violations kb))
         "the refused mint is recorded, carrying the refusal's kind"))))
