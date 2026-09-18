;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quote-test
  "Mention opacity for a `quoting_function` (`Quote`) — docs/nat.md, docs/equality.md.

  A `Quote` reified NAT names a term *as syntax*: `(cycl_constant (Quote Muffet))` reifies
  to `(cycl_constant K)`, an ordinary unary type membership on an opaque constant, reusing
  the NAT machinery with no new engine support.  What `quoting_function` adds is opacity in
  the equality congruence: a `rewriteOf` **spelling** rename reaches into the mention, but a
  `sameAs` / `equals` **identity** merge of the referent does not fold the quoted term."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(defn- declare-quote!
  "Declare `Quote` a reifiable quoting function whose reified constants are `cycl_expression`
  instances by default, with `cycl_constant` a subtype."
  [kb Quote cycl_expression cycl_constant]
  (v/assert kb (list 'genl cycl_expression 'thing)        'CxUniverse)
  (v/assert kb (list 'genl cycl_constant cycl_expression) 'CxUniverse)
  (v/assert kb (list 'reifiable_function Quote)            'CxUniverse)
  (v/assert kb (list 'quoting_function Quote)              'CxUniverse)
  (v/assert kb (list 'result Quote cycl_expression)    'CxUniverse))

(defn- k-of [kb h] (second (:sentence (v/sentex kb h))))

(tu/deftest-kb a-quoted-term-reifies-and-is-typed-as-syntax
  (tu/with-terms [Quote Muffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [h (v/assert kb (list cycl_constant (list Quote Muffet)) 'CxUniverse)
          k (k-of kb h)]
      (is (nat/reified-nat-symbol? k) "the quoted term reifies to an opaque constant")
      (is (= (list Quote Muffet) (nat/nat-expression kb k)))
      (is (v/isa? kb k cycl_constant 'CxUniverse)   "K is a cycl_constant")
      (is (v/isa? kb k cycl_expression 'CxUniverse) "and a cycl_expression up the genl"))))

(tu/deftest-kb sameas-does-not-fold-a-quoted-term
  ;; The opacity: merging the *referents* Muffet and Fluffet leaves the two *terms* — and
  ;; so the two reified quoted constants — distinct, because a mention tracks identity of
  ;; the symbol, not of what it denotes.
  (tu/with-terms [Quote Muffet Fluffet cycl_expression cycl_constant]
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
  (tu/with-terms [Quote Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote Muffet))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote Fluffet)) 'CxUniverse))]
      (is (not= k1 k2))
      (v/assert kb (list 'rewriteOf Fluffet Muffet) 'CxUniverse)   ; Muffet deprecated -> Fluffet
      (testing "the quoted expression is rewritten by the spelling rename and folds"
        (is (empty? (nat/colliding-constant-groups kb)) "the collision is repaired to one")
        (is (some? (nat/dedup-constant kb (list Quote Fluffet))))
        (is (= (nat/dedup-constant kb (list Quote Fluffet))
               (nat/dedup-constant kb (list Quote Muffet)))
            "the retired spelling still resolves to the merged constant")))))

(tu/deftest-kb a-non-quoting-reifiable-nat-still-folds-on-a-spelling-merge
  ;; Control: mention opacity is specific to a quoting_function.  A plain reifiable NAT's
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
;; rename reaches it just the same.  The bare-symbol tests above pin depth 1; these pin
;; the recursion.

(tu/deftest-kb sameas-does-not-fold-a-referent-nested-in-a-quoted-compound
  (tu/with-terms [Quote foo Muffet Fluffet cycl_expression cycl_constant]
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
  (tu/with-terms [Quote foo Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote (list foo Muffet)))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote (list foo Fluffet))) 'CxUniverse))]
      (is (not= k1 k2))
      (v/assert kb (list 'rewriteOf Fluffet Muffet) 'CxUniverse)   ; nested Muffet -> Fluffet
      (testing "the nested spelling rename reaches into the mention and folds it"
        (is (empty? (nat/colliding-constant-groups kb)))
        (is (= (nat/dedup-constant kb (list Quote (list foo Fluffet)))
               (nat/dedup-constant kb (list Quote (list foo Muffet)))))))))

(tu/deftest-kb a-transitive-spelling-chain-folds-a-quoted-term
  ;; `spelling-representative` walks the whole rewriteOf-connected component, so a two-hop
  ;; rename `A -> B -> C` resolves `(Quote A)` to `(Quote C)` — the single-hop test above
  ;; leaves the loop unexercised.
  (tu/with-terms [Quote A B C cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [ka (k-of kb (v/assert kb (list cycl_constant (list Quote A)) 'CxUniverse))
          kc (k-of kb (v/assert kb (list cycl_constant (list Quote C)) 'CxUniverse))]
      (is (not= ka kc))
      (v/assert kb (list 'rewriteOf B A) 'CxUniverse)   ; A -> B
      (v/assert kb (list 'rewriteOf C B) 'CxUniverse)   ; B -> C
      (testing "the two-hop spelling chain reaches the mention and folds it"
        (is (empty? (nat/colliding-constant-groups kb)))
        (is (= (nat/dedup-constant kb (list Quote C))
               (nat/dedup-constant kb (list Quote A)))
            "the head of the chain still resolves the retired spelling")))))

;; ---- orthogonality: quoting is not reifiability --------------------------
;; The comment on the prop and CxCore both say quoting governs argument opacity, not
;; whether the application is minted: `Quasiquote` is unreifiable AND quoting.  So the
;; combination the reifiable `Quote` tests never reach is a mention that stays structural
;; — never minted — yet whose referents an identity merge still may not fold.

(tu/deftest-kb an-unreifiable-quoting-function-keeps-a-structural-mention-opaque
  (tu/with-terms [Quasiquote PlainFn Muffet Fluffet Obj p]
    (v/assert kb (list 'unreifiable_function Quasiquote) 'CxUniverse)
    (v/assert kb (list 'quoting_function Quasiquote)     'CxUniverse)
    (v/assert kb (list 'unreifiable_function PlainFn)    'CxUniverse)
    (v/assert kb (list 'sameAs Muffet Fluffet)          'CxUniverse)
    (testing "the quoting mention stays structural — never minted"
      (let [h (v/assert kb (list p Obj (list Quasiquote Muffet)) 'CxUniverse)]
        (is (= (list p Obj (list Quasiquote Muffet)) (:sentence (v/sentex kb h))))
        (is (nil? (nat/dedup-constant kb (list Quasiquote Muffet))))))
    (testing "and a sameAs merge does not make two quoted mentions congruent"
      (is (v/ask? kb (list 'different (list Quasiquote Muffet) (list Quasiquote Fluffet))
                  'CxUniverse)))
    (testing "while a non-quoting unreifiable function's arguments still fold"
      (is (not (v/ask? kb (list 'different (list PlainFn Muffet) (list PlainFn Fluffet))
                       'CxUniverse))))))

;; ---- the gate does not disturb ordinary congruence -----------------------

(tu/deftest-kb a-quoting-declaration-does-not-block-ordinary-congruence
  ;; The gate turns the mention walk ON for the whole KB, but a NON-quoting compound must
  ;; still fold under a sameAs identity merge — the mention only spelling-restricts a
  ;; quoting head's own arguments.  A regression defaulting the walk to spelling would
  ;; break `(F 5 Kilogram) = (F 5 Kg)` congruence, but only once some quoting function is
  ;; also declared — a hole no gate-off test can see.
  (tu/with-terms [Quote Kilogram Kg QuantityFn cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)      ; gate ON
    (is (true? (tax/any-quoting-functions? (reasoning/taxonomy kb))))
    (v/assert kb (list 'sameAs Kilogram Kg) 'CxUniverse)
    (let [q (fn [u] (list QuantityFn 5 u))]
      (testing "a non-quoting compound still folds under congruence with the gate on"
        (is (not (v/ask? kb (list 'different (q Kilogram) (q Kg)) 'CxUniverse))))
      (testing "and an unmerged magnitude still tells two compounds apart"
        (is (v/ask? kb (list 'different (q Kilogram) (list QuantityFn 6 Kg)) 'CxUniverse))))))

;; ---- recover -------------------------------------------------------------

(tu/deftest-kb mention-opacity-survives-recover
  ;; the `:quoting` prop is a taxonomy mark rebuilt from the stored `(quoting_function Q)`
  ;; fact, so a rebuild must reconstruct the gate — else a recovered KB would start
  ;; folding a mention the running one held opaque, a restart changing an answer.
  (tu/with-terms [Quote Muffet Fluffet cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (let [k1 (k-of kb (v/assert kb (list cycl_constant (list Quote Muffet))  'CxUniverse))
          k2 (k-of kb (v/assert kb (list cycl_constant (list Quote Fluffet)) 'CxUniverse))]
      (v/recover kb)
      (testing "the gate rebuilds"
        (is (true? (tax/any-quoting-functions? (reasoning/taxonomy kb)))))
      (testing "so the mention is still opaque to an identity merge after recovery"
        (v/assert kb (list 'sameAs Muffet Fluffet) 'CxUniverse)
        (is (empty? (nat/colliding-constant-groups kb)))
        (is (not (v/same-class? kb k1 k2)))))))

;; ---- opacity reaches the REIFY pass, not only congruence ------------------
;; A compound mention whose payload contains a reifiable_function must not have that inner
;; NAT reified *by identity* — `reify-or-mint-nat` would otherwise fold two quoted syntaxes
;; whose payloads' referents merged onto one constant, before congruence could protect them.

(tu/deftest-kb a-reifiable-payload-inside-a-quote-is-not-folded-by-a-sameas
  (tu/with-terms [Quote foo Muffet Fluffet cycl_expression cycl_constant]
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
  (tu/with-terms [Quote foo bar Muffet cycl_expression cycl_constant]
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
  (tu/with-terms [Quote knows Bob Rob Ann Zed cycl_expression cycl_constant]
    (declare-quote! kb Quote cycl_expression cycl_constant)
    (v/assert kb (list 'rewriteOf Rob Bob) 'CxUniverse)   ; used term Bob -> Rob (a spelling rename)
    (v/assert kb (list 'sameAs Ann Zed) 'CxUniverse)      ; quoted term Zed's referent merges (identity)
    (let [d (kb/displaced-terms kb (list knows Bob (list Quote Zed)) 'CxUniverse)]
      (is (= Rob (get d Bob)) "the used term is reported displaced by its spelling rename")
      (is (not (contains? d Zed))
          "the quoted mention is held opaque to the sameAs and is not reported displaced"))))
