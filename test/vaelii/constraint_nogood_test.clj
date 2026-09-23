;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-nogood-test
  "Definitional violations as **nogoods** rather than as a throw and a drop.

  Disjointness, functionality and asymmetry each convict by naming a second believed
  sentex.  That is a nogood in exactly the sense `S` against `(not S)` is one, and the
  engine already has a theory of those: defeat the weaker, represent an equal
  defeasible pair as a dilemma, report an equal known-true pair.  These tests pin the
  three places that theory now reaches, and the one place it deliberately does not.

  What is *not* softened, and is tested here as much as what is:

  * A **malformed** sentence still throws — `wff` is about the sentence, not about a
    pair, and there is nothing to weigh it against.
  * A violation **against known-true content** still refuses on the assert path,
    because admitting it and then defeating it stores something the KB will never
    believe.
  * An **argument constraint** (`arg` / `genlArg` / `interArg`) is convicted by the
    *absence* of a path from the argument's types to the constraint type — an
    open-world judgement with no opposing sentex — so it stays a refusal and, on the
    derivation path, a drop.
  * **`arity`** stays a refusal for a different reason, and `constraint-vocabulary-test`
    is where that is pinned: it *does* name an opposing sentex, and that sentex is the
    vocabulary entry the conviction is read through, so a nogood over the pair would
    defeat its own premise."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

;;; ── asymmetry: a relation declared not to hold both ways ──────────────

(tu/deftest-kb an-asymmetric-pair-at-default-is-a-represented-dilemma
  ;; The measured gap: `(asymmetric P)` refused only against known-true content, so at
  ;; the default strength a relation declared not to hold both ways held both ways and
  ;; nothing said so.  Every other :default/:default clash in this engine is a
  ;; represented dilemma; this one was silence.
  (tu/with-terms [typLarger dog_t cat_t]
    (v/assert kb (list 'asymmetric typLarger) 'CxUniverse)
    (v/assert kb (list typLarger dog_t cat_t) 'CxUniverse)
    (testing "the converse is still admitted — neither claim outranks the other"
      (is (v/assert kb (list typLarger cat_t dog_t) 'CxUniverse)))
    (testing "but the KB no longer holds it in silence"
      (let [cs (v/contradictions kb)]
        (is (= 1 (count cs)) "the pair is reported exactly once")
        (is (= #{(v/handle-of kb (list typLarger dog_t cat_t) 'CxUniverse)
                 (v/handle-of kb (list typLarger cat_t dog_t) 'CxUniverse)}
               (:nogood (first cs))))
        (is (= 2 (count (:sides (first cs))))
            "both sides' justifications, which is what an application ranks with")))
    (testing "and both stay believed — a dilemma is represented, not decided"
      (is (v/ask? kb (list typLarger dog_t cat_t) 'CxUniverse))
      (is (v/ask? kb (list typLarger cat_t dog_t) 'CxUniverse)))))

(tu/deftest-kb an-asymmetric-pair-against-known-true-content-is-still-refused
  ;; the line the other two checks are generalized to: it was always read off `:class`
  (tu/with-terms [typLarger dog_t cat_t]
    (v/assert kb (list 'asymmetric typLarger) 'CxUniverse)
    (v/assert kb (list typLarger dog_t cat_t) 'CxUniverse {:strength :monotonic})
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list typLarger cat_t dog_t) 'CxUniverse)))
    (testing "and nothing was stored by the refusal"
      (is (nil? (v/handle-of kb (list typLarger cat_t dog_t) 'CxUniverse))))))

;;; ── the assert path keeps its guardrail unless asked otherwise ────────

(tu/deftest-kb a-disjoint-clash-on-the-assert-path-still-refuses-by-default
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list cat_t Muffet) 'CxUniverse)))
    (is (nil? (v/handle-of kb (list cat_t Muffet) 'CxUniverse))
        "a refusal stores nothing")
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb the-assert-path-arbitrates-when-asked-to
  ;; `*arbitrate-constraints?*` is the policy extension point: whether a *writer* is told no is a
  ;; question about the application, not about the engine.  On, all three checks read
  ;; the one rule — refuse only against known-true content.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse)
        (testing "the clashing membership is admitted rather than refused"
          (is (v/assert kb (list cat_t Muffet) 'CxUniverse)))
        (testing "and the pair is a represented dilemma, both believed"
          (is (seq (v/sentexes-matching kb (list dog_t Muffet) 'CxUniverse)))
          (is (seq (v/sentexes-matching kb (list cat_t Muffet) 'CxUniverse)))
          (is (= 1 (count (v/contradictions kb)))))))))

(tu/deftest-kb arbitration-never-admits-a-clash-with-known-true-content
  ;; the one thing the var does not buy: admitting what the KB can never believe.
  ;; **Never** is two readings, and both have to hold: the membership it opposes is
  ;; known-true, *and* so is the separation that makes the two a pair.  A separation the
  ;; KB can be told otherwise about is one the sentence outlives, so the declaration is
  ;; known-true here — which is what the shipped upper ontology says of its own
  ;; (`resources/kb/upper/`, `(set/monotonic (disjoint …))`).
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list cat_t Muffet) 'CxUniverse)))
        (is (nil? (v/handle-of kb (list cat_t Muffet) 'CxUniverse)))))))

(tu/deftest-kb arbitration-admits-a-known-true-clash-whose-separation-is-defeasible
  ;; ...and the other half of that reading, which is what makes the refusal a function of
  ;; the KB rather than of the write.  Same known-true membership, same incoming
  ;; sentence; the only difference is that the separation is a `:default` claim, so a
  ;; later `(not (disjoint …))` retires the pair and the sentence a refusal would have
  ;; thrown away is one the KB goes on to believe.  Admitted and weighed instead, where
  ;; the arbitration can reach it.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
        (is (v/assert kb (list cat_t Muffet) 'CxUniverse))
        (testing "and the known-true side is the one belief keeps"
          (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
          (is (not (v/ask? kb (list cat_t Muffet) 'CxUniverse))))
        ;; What a *decided* verdict does when the separation is withdrawn afterwards is
        ;; the section below.
        ))))

(tu/deftest-kb the-functional-arm-reads-its-declaration-the-same-way
  ;; The second policy-gated kind, and the same reading one relation over: what makes two
  ;; fillers a clash is `(functional P)`, so a `:default` declaration is one a denial
  ;; retires and the second filler is admitted and weighed rather than thrown away.
  ;; Numbers, because two *symbols* under a functional predicate are co-reference and the
  ;; KB derives an equality instead (docs/equality.md).
  (binding [checks/*arbitrate-constraints?* true]
    (testing "a defeasible functionality admits the second filler"
      (tu/with-kb [kb]
        (tu/with-terms [ageOfx Aa]
          (v/assert kb (list 'binary_predicate ageOfx) 'CxUniverse)
          (v/assert kb (list 'functional ageOfx) 'CxUniverse)
          (v/assert kb (list ageOfx Aa 3) 'CxUniverse {:strength :monotonic})
          (is (v/assert kb (list ageOfx Aa 4) 'CxUniverse))
          (is (v/ask? kb (list ageOfx Aa 3) 'CxUniverse))
          (is (not (v/ask? kb (list ageOfx Aa 4) 'CxUniverse))))))
    (testing "and a known-true one still refuses it"
      (tu/with-kb [kb]
        (tu/with-terms [ageOfy Ab]
          (v/assert kb (list 'binary_predicate ageOfy) 'CxUniverse)
          (v/assert kb (list 'functional ageOfy) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list ageOfy Ab 3) 'CxUniverse {:strength :monotonic})
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list ageOfy Ab 4) 'CxUniverse)))
          (is (nil? (v/handle-of kb (list ageOfy Ab 4) 'CxUniverse))))))))

(tu/deftest-kb the-metatype-arm-reads-every-ingredient-and-not-only-the-mark
  ;; Three sentexes make a metatype separation — the mark on the collection, and each
  ;; type's membership of it — and every one of them has to hold for the two types to be
  ;; a pair.  So the weakest decides: a known-true mark over a membership the KB can be
  ;; told otherwise about is a separation a denial of that membership retires, and the
  ;; clash is weighed rather than refused.
  (binding [checks/*arbitrate-constraints?* true]
    (testing "a defeasible membership of the collection admits the clash"
      (tu/with-kb [kb]
        (tu/with-terms [species dog_t cat_t Muffet]
          (v/assert kb (list 'disjoint_metatype species) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list species dog_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list species cat_t) 'CxUniverse)
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (is (v/assert kb (list cat_t Muffet) 'CxUniverse))
          (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
          (is (not (v/ask? kb (list cat_t Muffet) 'CxUniverse))))))
    (testing "and all three known-true refuses it"
      (tu/with-kb [kb]
        (tu/with-terms [species dog_t cat_t Muffet]
          (v/assert kb (list 'disjoint_metatype species) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list species dog_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list species cat_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list cat_t Muffet) 'CxUniverse)))
          (is (nil? (v/handle-of kb (list cat_t Muffet) 'CxUniverse))))))))

(tu/deftest-kb the-sibling-arm-reads-the-steps-down-to-the-marked-parent
  ;; `(sibling_disjoint Root)` separates Root's specializations, so what makes each side
  ;; one of them is an ingredient of the derivation and not a premise of it.  A `:default`
  ;; `genl` edge into the clique is a step a denial takes away, after which the two types
  ;; are not siblings under that mark at all.
  (binding [checks/*arbitrate-constraints?* true]
    (testing "a defeasible step into the clique admits the clash"
      (tu/with-kb [kb]
        (tu/with-terms [root_t dog_t cat_t Muffet]
          (v/assert kb (list 'sibling_disjoint root_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list 'genl dog_t root_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list 'genl cat_t root_t) 'CxUniverse)
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (is (v/assert kb (list cat_t Muffet) 'CxUniverse))
          (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
          (is (not (v/ask? kb (list cat_t Muffet) 'CxUniverse))))))
    (testing "and a clique every step of which is known-true refuses it"
      (tu/with-kb [kb]
        (tu/with-terms [root_t dog_t cat_t Muffet]
          (v/assert kb (list 'sibling_disjoint root_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list 'genl dog_t root_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list 'genl cat_t root_t) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list cat_t Muffet) 'CxUniverse)))
          (is (nil? (v/handle-of kb (list cat_t Muffet) 'CxUniverse))))))))

(tu/deftest-kb the-cover-arm-reads-the-declaration-that-separates-the-parts
  ;; `(partition Whole P1 P2)` separates its parts and writes the `genl` edges they rest
  ;; on, so one declaration is the whole derivation and its own class is the answer.
  (binding [checks/*arbitrate-constraints?* true]
    (testing "a defeasible partition admits the clash"
      (tu/with-kb [kb]
        (tu/with-terms [animal_t dog_t cat_t Muffet]
          (v/assert kb (list 'partition animal_t dog_t cat_t) 'CxUniverse)
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (is (v/assert kb (list cat_t Muffet) 'CxUniverse))
          (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
          (is (not (v/ask? kb (list cat_t Muffet) 'CxUniverse))))))
    (testing "and a known-true one refuses it"
      (tu/with-kb [kb]
        (tu/with-terms [animal_t dog_t cat_t Muffet]
          (v/assert kb (list 'partition animal_t dog_t cat_t) 'CxUniverse
                    {:strength :monotonic})
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list cat_t Muffet) 'CxUniverse)))
          (is (nil? (v/handle-of kb (list cat_t Muffet) 'CxUniverse))))))))

(tu/deftest-kb the-functional-mark-is-read-in-either-spelling-and-down-the-hierarchy
  ;; `(functional P)` speaks at argument 2 and `(functionalInArg P 2)` at the position it
  ;; names; either carries the constraint alone, so the mark holds as strongly as its
  ;; better spelling.  And a mark written of a general predicate reaches a specific one
  ;; over `genl` edges, which are ingredients like any other: a defeasible descent is a
  ;; descent a denial takes away.
  (binding [checks/*arbitrate-constraints?* true]
    (testing "a defeasible spelling beside a known-true one still refuses"
      (tu/with-kb [kb]
        (tu/with-terms [ageOfp Ac]
          (v/assert kb (list 'binary_predicate ageOfp) 'CxUniverse)
          (v/assert kb (list 'functional ageOfp) 'CxUniverse)
          (v/assert kb (list 'functionalInArg ageOfp 2) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list ageOfp Ac 3) 'CxUniverse {:strength :monotonic})
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list ageOfp Ac 4) 'CxUniverse))))))
    (testing "a defeasible descent to the predicate the sentence names admits the clash"
      (tu/with-kb [kb]
        (tu/with-terms [measureOfq ageOfq Ad]
          (v/assert kb (list 'binary_predicate measureOfq) 'CxUniverse)
          (v/assert kb (list 'binary_predicate ageOfq) 'CxUniverse)
          (v/assert kb (list 'functional measureOfq) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list 'genl ageOfq measureOfq) 'CxUniverse)
          (v/assert kb (list ageOfq Ad 3) 'CxUniverse {:strength :monotonic})
          (is (v/assert kb (list ageOfq Ad 4) 'CxUniverse))
          (is (v/ask? kb (list ageOfq Ad 3) 'CxUniverse))
          (is (not (v/ask? kb (list ageOfq Ad 4) 'CxUniverse))))))
    (testing "and a known-true descent refuses it"
      (tu/with-kb [kb]
        (tu/with-terms [measureOfr ageOfr Ae]
          (v/assert kb (list 'binary_predicate measureOfr) 'CxUniverse)
          (v/assert kb (list 'binary_predicate ageOfr) 'CxUniverse)
          (v/assert kb (list 'functional measureOfr) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list 'genl ageOfr measureOfr) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list ageOfr Ae 3) 'CxUniverse {:strength :monotonic})
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list ageOfr Ae 4) 'CxUniverse))))))))

(tu/deftest-kb the-grounds-read-takes-the-strongest-route-and-not-the-first
  ;; The grounds of a separation are a `genl` walk up from each side, and a type with two
  ;; parents has two routes to the same supertype.  `reach-strength` names the
  ;; *widest-bottleneck* route — the one whose weakest edge is strongest — so a defeasible
  ;; route beside a known-true one costs the refusal nothing, and only a defeasible step
  ;; every route passes through makes the derivation defeasible.
  ;;
  ;; The read that stops at the first route it finds gets the middle case wrong, and the
  ;; read that enumerates the routes instead of walking the adjacency gets it right and
  ;; pays a path per answer (`bench/vaelii/bench/perf.clj`,
  ;; `refusal-grounds-reading`).
  (binding [checks/*arbitrate-constraints?* true]
    (let [ladder (fn [kb [bot mid1 mid2 top other_t otop_t X] up1 up2]
                   (v/assert kb (list 'genl bot mid1) 'CxUniverse {:strength :monotonic})
                   (v/assert kb (list 'genl bot mid2) 'CxUniverse {:strength :monotonic})
                   (v/assert kb (list 'genl mid1 top) 'CxUniverse {:strength up1})
                   (v/assert kb (list 'genl mid2 top) 'CxUniverse {:strength up2})
                   (v/assert kb (list 'genl other_t otop_t) 'CxUniverse {:strength :monotonic})
                   (v/assert kb (list 'disjoint top otop_t) 'CxUniverse {:strength :monotonic})
                   (v/assert kb (list other_t X) 'CxUniverse {:strength :monotonic}))]
      (testing "every route known-true refuses the arriving membership"
        (tu/with-kb [kb]
          (tu/with-terms [bot_t mid1_t mid2_t top_t other_t otop_t Xa]
            (ladder kb [bot_t mid1_t mid2_t top_t other_t otop_t Xa] :monotonic :monotonic)
            (is (thrown? clojure.lang.ExceptionInfo
                         (v/assert kb (list bot_t Xa) 'CxUniverse)))
            (is (nil? (v/handle-of kb (list bot_t Xa) 'CxUniverse))))))
      ;; both arrangements, since which of the two parents a shortest-path walk would
      ;; reach first is a function of their minted names and not of the test
      (doseq [[up1 up2] [[:default :monotonic] [:monotonic :default]]]
        (testing (str "one defeasible route beside a known-true one refuses it too, "
                      up1 " then " up2)
          (tu/with-kb [kb]
            (tu/with-terms [bot_t mid1_t mid2_t top_t other_t otop_t Xb]
              (ladder kb [bot_t mid1_t mid2_t top_t other_t otop_t Xb] up1 up2)
              (is (thrown? clojure.lang.ExceptionInfo
                           (v/assert kb (list bot_t Xb) 'CxUniverse)))
              (is (nil? (v/handle-of kb (list bot_t Xb) 'CxUniverse)))))))
      (testing "and only a defeasible step on every route admits it"
        (tu/with-kb [kb]
          (tu/with-terms [bot_t mid1_t mid2_t top_t other_t otop_t Xc]
            (ladder kb [bot_t mid1_t mid2_t top_t other_t otop_t Xc] :default :default)
            (is (v/assert kb (list bot_t Xc) 'CxUniverse))
            (is (v/ask? kb (list other_t Xc) 'CxUniverse))
            (is (not (v/ask? kb (list bot_t Xc) 'CxUniverse)))))))))

;;; ── a verdict lives as long as its grounds ────────────────────────────

(tu/deftest-kb defeating-the-separation-revives-the-loser-decided-or-not
  ;; A separation losing to a known-true denial does not lose *to* the pair it separated:
  ;; it retires that pair.  `clear-defeats!` re-believes the declaration at the top of
  ;; every settle, so a verdict taken in the same round as the declaration's own defeat is
  ;; re-taken on a declaration that settle goes on to disbelieve — standing for as long as
  ;; both records do, with `disjoint?` answering false and `why-not` naming nothing.
  (binding [checks/*arbitrate-constraints?* true]
    (doseq [dog-strength [:monotonic :default]]
      (testing (str "with the pair " (if (= :monotonic dog-strength) "decided" "a dilemma"))
        (tu/with-kb [kb]
          (tu/with-terms [dog_t cat_t Muffet]
            (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
            (v/assert kb (list cat_t Muffet) 'CxUniverse)
            (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength dog-strength})
            (v/assert kb (list 'not (list 'disjoint dog_t cat_t)) 'CxUniverse
                      {:strength :monotonic})
            (is (not (v/disjoint? kb dog_t cat_t)))
            (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
            (is (v/ask? kb (list cat_t Muffet) 'CxUniverse)
                "the loser comes back with the separation that convicted it")
            (is (empty? (v/contradictions kb)))
            (is (:believed? (v/why-not kb (list cat_t Muffet) 'CxUniverse))
                "and nothing is left defeated by a pair no reader can name")))))))

(tu/deftest-kb defeating-the-edge-a-separation-is-read-over-revives-the-loser
  ;; The same reading one relation over, and the arm `scoped_defeat_test` covers only at a
  ;; vantage below the edge: an edge denied in the edge's own context is a global defeat,
  ;; so it is not the scoped kind the resolution already takes first.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [chi_t dog_t cat_t Kit]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list 'genl chi_t dog_t) 'CxUniverse)
        (v/assert kb (list chi_t Kit) 'CxUniverse)
        (v/assert kb (list cat_t Kit) 'CxUniverse {:strength :monotonic})
        (is (not (v/ask? kb (list chi_t Kit) 'CxUniverse)) "decided against the membership")
        (v/assert kb (list 'not (list 'genl chi_t dog_t)) 'CxUniverse {:strength :monotonic})
        (is (not (v/disjoint? kb chi_t cat_t)))
        (is (v/ask? kb (list chi_t Kit) 'CxUniverse))
        (is (v/ask? kb (list cat_t Kit) 'CxUniverse))))))

(tu/deftest-kb defeating-a-functionality-revives-the-filler-it-convicted
  ;; The second policy-gated kind, whose mark is withdrawn the same way.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [ageOfs Af]
        (v/assert kb (list 'binary_predicate ageOfs) 'CxUniverse)
        (v/assert kb (list 'functional ageOfs) 'CxUniverse)
        (v/assert kb (list ageOfs Af 3) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list ageOfs Af 4) 'CxUniverse)
        (is (not (v/ask? kb (list ageOfs Af 4) 'CxUniverse)))
        (v/assert kb (list 'not (list 'functional ageOfs)) 'CxUniverse {:strength :monotonic})
        (is (v/ask? kb (list ageOfs Af 3) 'CxUniverse))
        (is (v/ask? kb (list ageOfs Af 4) 'CxUniverse))))))

(tu/deftest-kb retracting-the-separation-revives-the-loser-as-it-always-did
  ;; The path that already worked, and the reason the denial did not: a retraction drops
  ;; the flat-cache entry before any settle runs, so the discovery never sees the pair.
  ;; It is here so a change to the denial half cannot quietly cost the retraction half.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (let [d (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)]
          (v/assert kb (list cat_t Muffet) 'CxUniverse)
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (is (not (v/ask? kb (list cat_t Muffet) 'CxUniverse)))
          (v/retract! kb d)
          (is (not (v/disjoint? kb dog_t cat_t)))
          (is (v/ask? kb (list cat_t Muffet) 'CxUniverse))
          (is (v/ask? kb (list dog_t Muffet) 'CxUniverse)))))))

;;; ── what stays a refusal ──────────────────────────────────────────────

(tu/deftest-kb a-malformed-sentence-still-throws-however-the-policy-is-set
  ;; `wff` is about the sentence.  There is no second believed sentex to weigh it
  ;; against, so there is nothing for `settle` to arbitrate and softening it would
  ;; simply store nonsense.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t Muffet]
        (testing "a genl cycle"
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list 'genl dog_t dog_t) 'CxUniverse))))
        (testing "a genl of an individual"
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list 'genl Muffet dog_t) 'CxUniverse))))
        (testing "a non-ground fact"
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list dog_t '?x) 'CxUniverse))))))))

(tu/deftest-kb an-argument-constraint-is-not-a-nogood
  ;; It convicts by the *absence* of a path from the argument's types to the constraint
  ;; type — negation as failure, not a stored sentex — so there is no pair to make and
  ;; it stays a refusal at the entry point and a drop at the firing.
  ;; Pinned to the constraint reading, which is the reading that has the conviction this
  ;; describes.  With the entailment on the declaration mints the type instead, so there is
  ;; no conviction-by-absence to classify; a mint the KB cannot admit refuses the fact that
  ;; entails it, and refuses under either policy (docs/argtypes.md).
  (tu/without-entailing
   (binding [checks/*arbitrate-constraints?* true]
     (tu/with-kb [kb]
       (tu/with-terms [person_t rock_t parentOf Boulder Muffet]
         (v/assert kb (list 'genl person_t 'thing) 'CxUniverse)
         (v/assert kb (list 'genl rock_t 'thing) 'CxUniverse)
         (v/assert kb (list 'arg parentOf 1 person_t) 'CxUniverse)
         (v/assert kb (list rock_t Boulder) 'CxUniverse)
         (is (thrown? clojure.lang.ExceptionInfo
                      (v/assert kb (list parentOf Boulder Muffet) 'CxUniverse))
             "refused at the entry point even with arbitration on")
         (is (empty? (v/contradictions kb))))))))

;;; ── the loser has a reason ────────────────────────────────────────────

(tu/deftest-kb an-arbitrated-loser-is-stored-and-has-a-why-not
  ;; the point of arbitrating rather than dropping: a dropped conclusion leaves no
  ;; record, so `why-not` can only say `:not-stored`
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x))))
              'CxUniverse)
    (let [h (v/handle-of kb (list fish_t Rex) 'CxUniverse)]
      (is (integer? h) "the conclusion is placed, not discarded")
      (is (not (v/in? kb h)))
      (is (= :defeated (:reason (v/why-not kb h)))))))

;;; ── what the report says ──────────────────────────────────────────────

(tu/deftest-kb a-definitional-dilemma-names-the-constraint-it-violated
  ;; a rebuttal and a definitional clash are both dilemmas and both stay believed, so
  ;; without `:kind` they read alike — and they are not alike
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'CxUniverse)
    (testing "a definitional clash names its constraint"
      (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))
    (testing "and ranks above a rebuttal"
      (is (every? #(<= 3 (:priority %)) (v/contradictions kb))))))

(tu/deftest-kb a-rebuttal-dilemma-has-no-constraint-to-name
  (tu/with-terms [flies Opus]
    (v/assert kb (list flies Opus) 'CxUniverse)
    (v/assert kb (list 'not (list flies Opus)) 'CxUniverse)
    (testing "a rebuttal names none"
      (is (= [nil] (mapv :kind (v/contradictions kb)))))
    (testing "and ranks below a definitional clash"
      (is (every? #(<= (:priority %) 2) (v/contradictions kb))))))

(tu/deftest-kb a-clash-is-reported-never-stored
  ;; `(contradicts X Y)` is a report form, not a sentex — asserting one would make it a
  ;; premise needing truth maintenance of its own, and it would go stale the moment
  ;; either side moved.  CxCore says so of the predicate; this holds the engine to
  ;; it, since the report *reads* like a sentence and the mistake would be invisible.
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (let [before (v/sentex-count kb)]
      (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'CxUniverse)
      (let [reported (:sentence (first (v/contradictions kb)))]
        (is (= 'contradicts (first reported)) "the report is indistinguishable from a sentence")
        (is (zero? (count (v/sentexes-with-functor kb 'contradicts)))
            "and is stored nowhere")
        (is (nil? (v/handle-of kb reported 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb (list 'contradicts '?a '?b) '?ctx)))
        (is (= (+ 2 before) (v/sentex-count kb))
            "the rule and its conclusion, and nothing for the clash")))))

(def ^:private report-keys
  "Every key a standing clash is reported with, whichever reading found it."
  #{:nogood :priority :sentence :handles :kind :sides})

(tu/deftest-kb an-irreducible-conflict-reports-the-full-shape
  ;; `conflicts` reports the same full shape `contradictions` does.  Handing back the
  ;; raw nogood here instead would give the *harder* case — where the engine has
  ;; declined hardest and the application has the most to do — the least to do it with.
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    (v/assert-rule kb [(list dog_t '?x)] (list fish_t '?x) 'CxUniverse {:direction :forward})
    (let [c (first (v/conflicts kb))]
      (is (some? c) "an irreducible known-true clash")
      (is (= report-keys (into #{} (keys c))))
      (is (= :disjoint (:kind c)))
      (is (= 2 (count (:sides c))))
      (is (every? #(contains? % :justifications) (:sides c))
          "including what each side rests on — the material an application acts on")
      (is (= [:monotonic :monotonic] (mapv :defeat-class (:sides c)))))))

(tu/deftest-kb a-dilemma-reports-the-same-shape-as-a-conflict
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'CxUniverse)
    (is (= report-keys (into #{} (keys (first (v/contradictions kb)))))
        "the two readings differ in why the pair stands, not in what is reported")))

;;; ── the candidate set does not grow without bound ─────────────────────

(tu/deftest-kb a-pair-that-stops-clashing-leaves-the-candidate-set
  ;; `:clashes` is what lets a standing dilemma outlive the settle that found it, so it
  ;; is consulted every settle — which means a pair that has stopped clashing and is
  ;; never forgotten costs an `arbitrable-violations` call per settle, forever.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse)
        (v/assert kb (list cat_t Muffet) 'CxUniverse)
        (is (= 1 (count (:pairs @(reasoning/clashes kb)))) "the pair is remembered")
        (testing "retracting the separation retires it, and it is forgotten"
          (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'CxUniverse))
          (is (empty? (v/contradictions kb)))
          (is (empty? (:pairs @(reasoning/clashes kb)))
              "both members still stored and believed, and they no longer clash"))
        (testing "and re-declaring it finds the pair again through the region"
          (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
          (is (= 1 (count (v/contradictions kb)))))))))

(tu/deftest-kb retracting-one-functional-in-arg-position-retires-a-pair-the-other-does-not-hold
  ;; `clash-vocabulary` fingerprints the `functionalInArg` **table** (`pred ->
  ;; #{positions}`), not the predicate roster: a predicate may carry two positions and
  ;; each is an independent constraint, so retracting `(functionalInArg P 1)` while
  ;; `(functionalInArg P 2)` stands must retire a pair position 1 alone convicted.  A
  ;; roster keyed on the predicate would leave P marked, the vocabulary value unmoved,
  ;; and a pair convicted only through the retracted position carried forward stale — a
  ;; `contradictions` report that depends on a declaration that is gone.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [linkPred Shared]
        (v/assert kb (list 'functionalInArg linkPred 1) 'CxUniverse)
        (v/assert kb (list 'functionalInArg linkPred 2) 'CxUniverse)
        ;; numbers in the constrained slot (argument 1) are unmergeable, so a shared
        ;; determinant (argument 2) is a real clash rather than a merge; the determinants
        ;; differ under position 2, so only position 1 convicts this pair
        (v/assert kb (list linkPred 1 Shared) 'CxUniverse)
        (v/assert kb (list linkPred 2 Shared) 'CxUniverse)
        (is (= 1 (count (:pairs @(reasoning/clashes kb)))) "position 1 convicts the pair")
        (is (= 1 (count (v/contradictions kb))))
        (testing "retracting position 1 retires it, though position 2 keeps linkPred marked"
          (v/retract! kb (v/handle-of kb (list 'functionalInArg linkPred 1) 'CxUniverse))
          (is (empty? (v/contradictions kb))
              "the constraint that convicted the pair is gone")
          (is (empty? (:pairs @(reasoning/clashes kb)))
              "and the pair is forgotten, not carried forward stale"))))))

(tu/deftest-kb a-standing-pair-is-not-re-derived-by-an-unrelated-settle
  ;; `:clashes` is consulted every settle and a settle runs after every mutation, so
  ;; re-deriving every standing pair each time makes loading N clashing facts O(N²) —
  ;; the shape docs/nmtms.md records for the defaults phase.  Measured before the memo:
  ;; one assert at 300 standing clashes took 36ms against 8ms at 50.
  ;;
  ;; Pinned by **object identity** rather than by a clock: a carried entry is the very
  ;; map the previous settle produced, which is only true if nothing re-derived it.  A
  ;; timing assertion would be flaky; this cannot be.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Muffet Rex]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse)
        (v/assert kb (list cat_t Muffet) 'CxUniverse)
        (let [pair  (first (keys (:nogoods @(reasoning/clashes kb))))
              entry (get (:nogoods @(reasoning/clashes kb)) pair)]
          (is (some? entry))
          (testing "a settle that moves nothing of the pair's carries it forward"
            (v/assert kb (list dog_t Rex) 'CxUniverse)
            (is (identical? entry (get (:nogoods @(reasoning/clashes kb)) pair))
                "re-derived, so the memo is not being used"))
          (testing "and moving the vocabulary does re-derive it"
            ;; the separation itself changing is what the memo may never take on trust
            (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'CxUniverse))
            (is (nil? (get (:nogoods @(reasoning/clashes kb)) pair)))
            (is (empty? (v/contradictions kb)))))))))

(tu/deftest-kb a-pair-with-a-defeated-member-is-kept
  ;; the other side of the pruning rule: a check cannot see past a defeat to say whether
  ;; the pair would still clash, so forgetting it would mean a revival went unreported
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x))))
              'CxUniverse)
    (let [h (v/handle-of kb (list fish_t Rex) 'CxUniverse)]
      (is (not (v/in? kb h)) "the derived side lost")
      (is (= 1 (count (:pairs @(reasoning/clashes kb))))
          "and the pair is retained, so the clash is re-reported if it revives"))))

(tu/deftest-kb a-carried-report-still-names-a-side-s-second-derivation
  ;; The *report* is memoized on the settle's region beside the nogood itself, and one
  ;; part of it does not follow the region.  A **redundant** justification — a second
  ;; derivation of an already-believed conclusion, conferring no stronger a class — is
  ;; exactly the write the JTMS declines to relabel for, so a side's supporting set grows
  ;; while its handle never enters a region.  The justifications behind each side are what
  ;; a caller ranks a dilemma with, so a report carried past that is a report naming fewer
  ;; reasons than the KB holds.  `nmtms_test` pins the same property for a plain rebuttal;
  ;; here the whole chain — `:clashes`, then `:reports` — is the definitional one.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Rex markA markB]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Rex) 'CxUniverse)
        (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list markA '?x)] (list cat_t '?x))))
                  'CxUniverse)
        (v/assert kb (list markA Rex) 'CxUniverse)
        (let [h (v/handle-of kb (list cat_t Rex) 'CxUniverse)]
          (is (= 1 (count (v/contradictions kb))) "a default/default clash is a dilemma")
          (is (v/in? kb h))
          ;; a second rule reaching the same conclusion: belief is unmoved, so no relabel
          (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list markB '?x)] (list cat_t '?x))))
                    'CxUniverse)
          (v/assert kb (list markB Rex) 'CxUniverse)
          (is (= 2 (count (v/supporting-justifications kb h))))
          (let [side (some (fn [c] (some #(when (= h (:handle %)) %) (:sides c)))
                           (v/contradictions kb))]
            (is (some? side))
            (is (= :disjoint (:kind (first (v/contradictions kb)))))
            (is (= (count (v/supporting-justifications kb h))
                   (count (:justifications side)))
                "the report names both derivations, not the one it named last settle")))))))

(tu/deftest-kb an-equal-known-true-clash-is-a-conflict-not-a-dilemma
  ;; the third branch of `decide-nogood`: neither side can be defeated, so it is
  ;; irreducible and reported by `conflicts` — never thrown from inside the fixpoint
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    ;; a bare rule confers :monotonic and is capped by its antecedent, so the
    ;; conclusion is known-true too and ties with the membership
    (v/assert-rule kb [(list dog_t '?x)] (list fish_t '?x) 'CxUniverse {:direction :forward})
    (let [cs (v/conflicts kb)]
      (is (= 1 (count cs)))
      (is (= :disjoint (:kind (first cs))))
      (is (= #{(v/handle-of kb (list dog_t Rex)  'CxUniverse)
               (v/handle-of kb (list fish_t Rex) 'CxUniverse)}
             (:nogood (first cs)))))
    (is (empty? (v/contradictions kb)) "an irreducible clash is not a dilemma")))

;;; ── recomputed, never accumulated ─────────────────────────────────────

(tu/deftest-kb a-dilemma-goes-when-its-ingredient-does-and-comes-back-with-it
  ;; the discipline belief itself follows: the pair is re-derived from current state
  ;; each settle, so retracting an ingredient retires it and restoring one revives it.
  ;; A ledger entry would do neither — which is the difference between arbitrating a
  ;; clash and filing a report about it.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse)
        (v/assert kb (list cat_t Muffet) 'CxUniverse)
        (is (= 1 (count (v/contradictions kb))))
        (testing "retracting one membership retires the pair"
          (v/retract! kb (v/handle-of kb (list cat_t Muffet) 'CxUniverse))
          (is (empty? (v/contradictions kb)))
          (is (seq (v/sentexes-matching kb (list dog_t Muffet) 'CxUniverse))
              "and leaves the survivor alone"))
        (testing "and asserting it again brings the pair back"
          (v/assert kb (list cat_t Muffet) 'CxUniverse)
          (is (= 1 (count (v/contradictions kb)))))
        (testing "retracting the *declaration* retires it too — nothing separates them now"
          (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'CxUniverse))
          (is (empty? (v/contradictions kb))))))))

(tu/deftest-kb an-arbitration-survives-a-rebuild
  ;; A nogood is *state*, not an event: belief depends on it.  The exposure pass beside
  ;; it sits out a rebuild because "newly exposed" is vacuous when everything arrives at
  ;; once — but a rebuild that skipped this would come up with the loser of a decided
  ;; clash believed again, and the KB would answer differently either side of a restart.
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x))))
              'CxUniverse)
    (let [h (v/handle-of kb (list fish_t Rex) 'CxUniverse)]
      (is (not (v/in? kb h)) "defeated before the rebuild")
      (v/recover kb)
      (is (not (v/in? kb h)) "and still defeated after it"))))

(tu/deftest-kb a-dilemma-survives-a-rebuild
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'CxUniverse)
    (is (= 1 (count (v/contradictions kb))) "a dilemma before the rebuild")
    (v/recover kb)
    (is (= 1 (count (v/contradictions kb))) "and the same dilemma after it")))

;;; ── a declaration reaching content stored before it ───────────────────

(tu/deftest-kb a-functional-declaration-arriving-last-is-arbitrated
  ;; the `predicate-sentexes` sweep: the two values were admissible when written,
  ;; because nothing said the predicate was functional yet
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [birthYearOf Tom]
        (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
        (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
        (is (empty? (v/contradictions kb)) "nothing says one value only, yet")
        (v/assert kb (list 'functional birthYearOf) 'CxUniverse)
        (is (= [:functional] (mapv :kind (v/contradictions kb))))))))

(tu/deftest-kb a-genl-edge-arriving-last-is-arbitrated
  ;; the `instances-below` sweep: the held types were not themselves separated until an
  ;; edge put one of them under a separated type
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t canine_t cat_t Rex]
        (v/assert kb (list 'genl canine_t 'thing) 'CxUniverse)
        (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
        (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
        (v/assert kb (list 'disjoint canine_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Rex) 'CxUniverse)
        (v/assert kb (list cat_t Rex) 'CxUniverse)
        (is (empty? (v/contradictions kb)) "a dog-cat is odd but nothing separates them")
        (v/assert kb (list 'genl dog_t canine_t) 'CxUniverse)
        (is (= [:disjoint] (mapv :kind (v/contradictions kb))))))))

(tu/deftest-kb a-disjoint-metatype-arriving-last-is-arbitrated
  ;; the `disjoint_metatype` sweep: the clique is a property of the code rather than
  ;; stored pairs, so the members have to be reached through `tax/metatype-members`
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [animal_species dog_t cat_t Muffet]
        (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
        (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
        (v/assert kb (list animal_species dog_t) 'CxUniverse)
        (v/assert kb (list animal_species cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse)
        (v/assert kb (list cat_t Muffet) 'CxUniverse)
        (is (empty? (v/contradictions kb)) "the metatype is not disjoint yet")
        (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
        (is (= [:disjoint] (mapv :kind (v/contradictions kb))))
        (testing "and dropping the metatype releases the pair, as it releases the clique"
          (v/retract! kb (v/handle-of kb (list 'disjoint_metatype animal_species) 'CxUniverse))
          (is (empty? (v/contradictions kb))))))))

(tu/deftest-kb a-metatype-member-arriving-last-is-arbitrated
  ;; the `metatype-member-reach` sweep, and the one trigger no functor names: a term
  ;; joining an already-disjoint metatype separates it from every member already there,
  ;; and the sentence saying so is an ordinary unary membership whose functor is
  ;; whatever the metatype happens to be called.  Only the taxonomy knows it declares
  ;; anything at all, so a fixed vocabulary of declaration functors cannot see it — and
  ;; the exposure pass, which reads the taxonomy, would report the pair while nothing
  ;; decided it.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [animal_species dog_t cat_t Muffet]
        (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
        (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
        (v/assert kb (list animal_species dog_t) 'CxUniverse)
        (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse)
        (v/assert kb (list cat_t Muffet) 'CxUniverse)
        (is (empty? (v/contradictions kb))
            "cat_t is not a member yet, so the metatype separates nothing from dog_t")
        (v/assert kb (list animal_species cat_t) 'CxUniverse)
        (is (v/disjoint? kb dog_t cat_t) "the clique closed over the arriving member")
        (is (= [:disjoint] (mapv :kind (v/contradictions kb)))
            "the pair the new member separates is exposed but never arbitrated")))))

(tu/deftest-kb a-genlcx-edge-arriving-last-is-arbitrated
  ;; the `members-in-ancestors` sweep: neither writer could see the other, so both
  ;; memberships were admissible — until a visibility edge put them in one ancestor set
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [CxA CxB t1 t2 Pip]
        (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
        (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
        (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
        (v/assert kb (list t1 Pip) CxA)
        (v/assert kb (list t2 Pip) CxB)
        (is (not (v/sees? kb CxB CxA)))
        (is (empty? (v/contradictions kb))
            "each is admissible where it was written — neither context sees the other")
        (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
        (is (= [:disjoint] (mapv :kind (v/contradictions kb)))
            "the visibility edge is what makes them a pair")))))

(tu/deftest-kb a-descended-functional-declaration-arriving-last-is-arbitrated
  ;; the `subtree-facts` sweep, and the reason a mark needs one where a separation does
  ;; not: the mark is read *up* the predicate hierarchy by the checks the entry point and this
  ;; sweep share (`tax/props-over`), so the facts a declaration reaches back over are the
  ;; whole subtree beneath the predicate it names.  Reading `measureOf`'s own posting list
  ;; is reading the one thing a general spelling is usually empty of.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [birthYearOf measureOf Tom]
        (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
        (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
        (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
        (is (empty? (v/contradictions kb)) "nothing above birthYearOf is marked, yet")
        (v/assert kb (list 'functional measureOf) 'CxUniverse)
        (is (= [:functional] (mapv :kind (v/contradictions kb))))))))

(tu/deftest-kb a-descended-asymmetric-declaration-arriving-last-is-arbitrated
  ;; the same sweep for the other mark: the converse probe fans down the hierarchy and
  ;; the mark is read up it, so both halves of the question descend or neither does
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [muchLargerThan largerThan Rex Pip]
        (v/assert kb (list muchLargerThan Rex Pip) 'CxUniverse)
        (v/assert kb (list muchLargerThan Pip Rex) 'CxUniverse)
        (v/assert kb (list 'genl muchLargerThan largerThan) 'CxUniverse)
        (is (empty? (v/contradictions kb)))
        (v/assert kb (list 'asymmetric largerThan) 'CxUniverse)
        (is (= [:asymmetric] (mapv :kind (v/contradictions kb))))))))

(tu/deftest-kb a-genl-edge-carrying-a-mark-down-is-arbitrated
  ;; the second reach a `genl` edge has, beside the memberships its type reading
  ;; implicates: a standing mark descends to a subtree that never carried one, so a pair
  ;; nothing separated a moment ago is a pair now, with neither fact relabelled
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [birthYearOf measureOf Tom]
        (v/assert kb (list 'functional measureOf) 'CxUniverse)
        (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
        (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
        (is (empty? (v/contradictions kb)) "the mark is above nothing they are under")
        (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
        (is (= [:functional] (mapv :kind (v/contradictions kb))))))))

(tu/deftest-kb a-descended-pair-joins-the-candidate-set-and-is-re-derived
  ;; **The sharp edge behind the miss, and why it was not merely a late report.**  A pair
  ;; the sweep never reaches never enters `:clashes`, and `:clashes` is the whole of what
  ;; makes discovery accumulate — so no later settle re-examines it, however many run.  A
  ;; third filler arriving through the entry point minted its own two pairs and left the first
  ;; one absent, which is a KB reporting two thirds of one slot's clashes.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [birthYearOf measureOf Tom Pip]
        (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
        (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
        (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
        (v/assert kb (list 'functional measureOf) 'CxUniverse)
        (is (= 1 (count (v/contradictions kb))) "the sweep found it")
        (testing "an unrelated settle re-derives it rather than losing it"
          (v/assert kb (list birthYearOf Pip 2000) 'CxUniverse)
          (is (= 1 (count (v/contradictions kb)))))
        (testing "and a third filler adds its two pairs beside the first, not instead of it"
          (v/assert kb (list birthYearOf Tom 2000) 'CxUniverse)
          (is (= #{:functional} (set (mapv :kind (v/contradictions kb)))))
          (is (= 3 (count (v/contradictions kb)))
              "three values of one slot are three pairs")
          (is (contains? (set (map :sentence (v/contradictions kb)))
                         (list 'contradicts (list birthYearOf Tom 1980)
                               (list birthYearOf Tom 1990)))
              "the originally-missed pair among them"))))))

;;; ── the pair only one context can see ─────────────────────────────────

;; A separation, a functional slot and an asymmetric claim are all checked against what
;; the *asking* context can see, which is right — a context is convicted only on
;; grounds it can see.  It leaves a pair whose halves sit either side of a `genlCx`
;; edge answerable from exactly one of the two contexts they are written in, so the
;; question has to be asked from there rather than from whichever half arrived last
;; (`settle/clash-askers`).

(defn- straddle-kb
  "A general context, one that sees it, and the declaration in `CxUniverse` — the
  lattice all three kinds are exercised over."
  [kb gen spec]
  (v/assert kb (list 'genlCx gen 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx spec gen) 'CxUniverse))

;; Each written **general-last**, which is the order the general side's own check cannot
;; answer: it sees neither the specific membership nor the specific claim.  One test per
;; kind, since a clash reported once is reported until its ingredients move and a second
;; scenario in the same KB would read the first one's answer.

(tu/deftest-kb a-separation-across-a-visibility-edge-is-arbitrated
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [CxGen CxSpec dog_t cat_t Muffet]
      (straddle-kb kb CxGen CxSpec)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list cat_t Muffet) CxSpec)
      (v/assert kb (list dog_t Muffet) CxGen)
      (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb a-functional-slot-filled-across-a-visibility-edge-is-arbitrated
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [CxGen CxSpec ageOf Tom]
      (straddle-kb kb CxGen CxSpec)
      (v/assert kb (list 'functional ageOf) 'CxUniverse)
      (v/assert kb (list ageOf Tom 6) CxSpec)
      (v/assert kb (list ageOf Tom 5) CxGen)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb an-asymmetric-converse-across-a-visibility-edge-is-arbitrated
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [CxGen CxSpec biggerThan Ann Bob]
      (straddle-kb kb CxGen CxSpec)
      (v/assert kb (list 'asymmetric biggerThan) 'CxUniverse)
      (v/assert kb (list biggerThan Bob Ann) CxSpec)
      (v/assert kb (list biggerThan Ann Bob) CxGen)
      (is (= [:asymmetric] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb known-true-content-does-not-coexist-with-a-default-that-denies-it
  ;; What the reporting gap costs: the general claim is admitted because its own context
  ;; cannot see the specific one, and without a vantage that can, a `:monotonic` claim
  ;; sits beside a `:default` the KB knows to be wrong.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [CxGen CxSpec animal_t plant_t Ox]
        (straddle-kb kb CxGen CxSpec)
        (v/assert kb (list 'disjoint animal_t plant_t) 'CxUniverse)
        (v/assert kb (list plant_t Ox) CxSpec)
        (v/assert kb (list animal_t Ox) CxGen {:strength :monotonic})
        (is (v/ask? kb (list animal_t Ox) CxGen))
        (is (not (v/ask? kb (list plant_t Ox) CxSpec))
            "the default loses to known-true content it could not see when it was written")
        (is (empty? (v/contradictions kb)) "decided, so there is no dilemma left to report")))))

(tu/deftest-kb a-membership-stated-in-two-visible-contexts-forms-two-pairs
  ;; One sentence stated in a general context and again in one that sees it is *two*
  ;; sentexes, of possibly different strength, and a third membership that denies the
  ;; type denies both.  Naming only the content-first of them left the other believed
  ;; beside content that contradicts it.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [CxGen CxSpec dog_t cat_t Muffet]
        (straddle-kb kb CxGen CxSpec)
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) CxGen)
        (v/assert kb (list dog_t Muffet) CxSpec)
        (v/assert kb (list cat_t Muffet) CxSpec)
        (is (= 2 (count (v/contradictions kb)))
            "one pair per opposing sentex, not one per opposing type")
        (is (= #{#{(v/handle-of kb (list cat_t Muffet) CxSpec)
                   (v/handle-of kb (list dog_t Muffet) CxGen)}
                 #{(v/handle-of kb (list cat_t Muffet) CxSpec)
                   (v/handle-of kb (list dog_t Muffet) CxSpec)}}
               (into #{} (map :nogood) (v/contradictions kb))))))))

(tu/deftest-kb a-pair-reachable-from-several-viewers-is-one-entry
  ;; Two incomparable siblings, and *two* contexts below both — so the pair has two
  ;; maximal common descendants and the check runs from each.  A nogood is keyed on the
  ;; handle pair and its sentence is content-ordered, so which viewer found it decides
  ;; nothing; an entry per viewer would report one clash twice and make the count a
  ;; property of the context lattice.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [CxA CxB CxK CxL t1 t2 Pip]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (doseq [k [CxK CxL]]
        (v/assert kb (list 'genlCx k CxA) 'CxUniverse)
        (v/assert kb (list 'genlCx k CxB) 'CxUniverse))
      (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
      (v/assert kb (list t1 Pip) CxA)
      (is (not (v/sees? kb CxB CxA)))
      (v/assert kb (list t2 Pip) CxB)
      (let [cs (v/contradictions kb)]
        (is (= 1 (count cs)) "one clash, however many contexts can see it")
        (is (= #{(v/handle-of kb (list t1 Pip) CxA)
                 (v/handle-of kb (list t2 Pip) CxB)}
               (:nogood (first cs))))
        (is (= :disjoint (:kind (first cs))))))))

(tu/deftest-kb a-retraction-that-splits-the-visibility-releases-the-pair
  ;; The other direction, and the one a maintained candidate set can get wrong: `:clashes`
  ;; is keyed on storage and recomputed from belief, so a pair whose *joint view* goes
  ;; away has to stop being reported and stop being remembered — not sit there costing an
  ;; `arbitrable-violations` call per settle for the rest of the KB's life.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [CxGen CxSpec dog_t cat_t Muffet]
        (straddle-kb kb CxGen CxSpec)
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list cat_t Muffet) CxSpec)
        (v/assert kb (list dog_t Muffet) CxGen)
        (is (= 1 (count (v/contradictions kb))))
        (is (= 1 (count (:pairs @(reasoning/clashes kb)))) "the pair is remembered")
        (testing "the edge leaving takes the joint view with it"
          (v/retract! kb (v/handle-of kb (list 'genlCx CxSpec CxGen)
                                      'CxUniverse))
          (is (not (v/sees? kb CxSpec CxGen)))
          (is (empty? (v/contradictions kb)))
          (is (empty? (:pairs @(reasoning/clashes kb)))
              "both members still believed, and no context sees them together")
          (is (v/ask? kb (list dog_t Muffet) CxGen))
          (is (v/ask? kb (list cat_t Muffet) CxSpec)))
        (testing "and the edge returning brings the pair back"
          (v/assert kb (list 'genlCx CxSpec CxGen) 'CxUniverse)
          (is (= 1 (count (v/contradictions kb)))))))))

;;; ── more than two ─────────────────────────────────────────────────────

(deftest ^:slow three-mutually-disjoint-memberships-report-all-three-pairs
  ;; A term holding three mutually disjoint types forms three pairs, and each stored
  ;; membership convicts against the other two.  The definitional checks stop at the
  ;; *first* violation, which is right for a refusal and wrong for discovery: which
  ;; partner each membership picked would come from the order the argument root handed
  ;; the memberships back — handle order, so arrival order.  Written as a permutation
  ;; because a count assertion alone would have passed while the *set* drifted.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(disjoint za zb) 'CxUniverse)
               #(v/assert % '(disjoint zb zc) 'CxUniverse)
               #(v/assert % '(disjoint za zc) 'CxUniverse)
               #(v/assert % '(za Pip) 'CxUniverse)
               #(v/assert % '(zb Pip) 'CxUniverse)
               #(v/assert % '(zc Pip) 'CxUniverse)]
          observe (fn [kb]
                    ;; the *set* of clashing sentence pairs, keyed on content — handles
                    ;; differ between orderings, so comparing them would prove nothing
                    {:pairs (into #{}
                                  (map (fn [c]
                                         (into #{} (map :sentence) (:sides c))))
                                  (v/contradictions kb))
                     :believed (count (filter #(seq (v/sentexes-matching kb (list % 'Pip) 'CxUniverse))
                                              '[za zb zc]))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "three-way clash: " (count os) " distinct outcomes across 720 orderings — "
               (pr-str os)))
      (testing "all three pairs, and all three memberships still believed"
        (is (= 3 (count (:pairs (first os)))))
        (is (= 3 (:believed (first os)))))
      (tu/clear-kb! (tu/test-kb)))))

(deftest an-antitransitive-triple-settles-the-same-way-in-every-arrival-order
  ;; A nogood of three, and the case a pairwise engine could not represent: the mark and
  ;; the three tuples in all 24 orders, landing on one belief set and one report.  Each
  ;; member convicts the other two (`checks/chain-triples`, three roles), so which of them
  ;; the region happened to hold last cannot decide whether the clash exists — and the
  ;; entry is keyed on the handle *set*, so a triple reached from three sides is one
  ;; dilemma rather than three.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(anti_transitive zprecedes) 'CxUniverse)
               #(v/assert % '(zprecedes Za Zb) 'CxUniverse)
               #(v/assert % '(zprecedes Zb Zc) 'CxUniverse)
               #(v/assert % '(zprecedes Za Zc) 'CxUniverse)]
          observe (fn [kb]
                    {:believed (into #{} (filter #(seq (v/sentexes-matching kb % 'CxUniverse)))
                                     '[(zprecedes Za Zb) (zprecedes Zb Zc) (zprecedes Za Zc)])
                     :clashes  (into #{}
                                     (map (fn [c] [(:kind c)
                                                   (into #{} (map :sentence) (:sides c))]))
                                     (v/contradictions kb))
                     :conflicts (count (v/conflicts kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "anti-transitive triple: " (count os) " distinct outcomes across 24 orderings — "
               (pr-str os)))
      (testing "one clash naming all three, and all three still believed"
        (is (= 3 (count (:believed (first os)))))
        (is (= 1 (count (:clashes (first os)))))
        (is (= [:anti-transitive] (mapv first (:clashes (first os)))))
        (is (= 3 (count (second (first (:clashes (first os)))))))
        (is (zero? (:conflicts (first os)))))
      (tu/clear-kb! (tu/test-kb)))))

(tu/deftest-kb a-derived-closing-step-is-placed-and-defeated-with-a-why-not
  ;; The firing row of the table in docs/nmtms.md, for the three-member nogood: a rule
  ;; has no caller to refuse, so the conclusion is placed and `settle` weighs it against
  ;; the chain — which is what leaves the loser a reason instead of `:not-stored`.
  (tu/with-terms [zprec zhints Qa Qb Qc]
    (v/assert kb (list 'anti_transitive zprec) 'CxUniverse)
    (v/assert kb (list zprec Qa Qb) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list zprec Qb Qc) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule
                       (list 'set/forwardRule (vr/rule-sentence [(list zhints '?x '?y)] (list zprec '?x '?y))))
              'CxUniverse)
    (v/assert kb (list zhints Qa Qc) 'CxUniverse)
    (let [h (v/handle-of kb (list zprec Qa Qc) 'CxUniverse)]
      (is (some? h) "the conclusion is stored rather than dropped")
      (is (not (v/in? kb h)) "and defeated, being the one defeasible member")
      (is (= :defeated (:reason (v/why-not kb h))))
      (is (every? #(v/ask? kb % 'CxUniverse) [(list zprec Qa Qb) (list zprec Qb Qc)])
          "the known-true chain is untouched"))))

(tu/deftest-kb an-antitransitive-triple-survives-a-rebuild
  ;; A nogood is state, and a three-member one is no different: a rebuild that came up
  ;; without it would believe the defeated step again and report no dilemma, so the KB
  ;; would answer differently either side of a restart.
  (tu/with-terms [zprec Ra Rb Rc]
    (v/assert kb (list 'anti_transitive zprec) 'CxUniverse)
    (v/assert kb (list zprec Ra Rb) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list zprec Rb Rc) 'CxUniverse)
    (v/assert kb (list zprec Ra Rc) 'CxUniverse {:strength :monotonic})
    (let [h (v/handle-of kb (list zprec Rb Rc) 'CxUniverse)]
      (is (not (v/in? kb h)) "the one defeasible step is defeated before the rebuild")
      (v/recover kb)
      (is (not (v/in? kb h)) "and still defeated after it"))))

(deftest an-antitransitive-declaration-arriving-last-is-arbitrated
  ;; The retroactive half, which `functional` and `asymmetric` already have: a mark
  ;; arriving over content stored long before it has to reach back over that content
  ;; (`settle/declaration-implicates`), or the answer would depend on whether the
  ;; declaration was written first.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [zprec Pa Pb Pc]
        (v/assert kb (list zprec Pa Pb) 'CxUniverse)
        (v/assert kb (list zprec Pb Pc) 'CxUniverse)
        (v/assert kb (list zprec Pa Pc) 'CxUniverse)
        (is (empty? (v/contradictions kb)))
        (v/assert kb (list 'anti_transitive zprec) 'CxUniverse)
        (let [cs (v/contradictions kb)]
          (is (= 1 (count cs)) "the declaration convicts what was already stored")
          (is (= :anti-transitive (:kind (first cs))))
          (is (= 3 (count (:sides (first cs))))))))))

(tu/deftest-kb a-functional-clash-on-the-assert-path-arbitrates-when-asked-to
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb]
      (tu/with-terms [birthYearOf Tom]
        (v/assert kb (list 'functional birthYearOf) 'CxUniverse)
        (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
        (testing "the second value is admitted rather than refused"
          (is (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)))
        (is (= [:functional] (mapv :kind (v/contradictions kb))))))))

;;; ── order independence, tested directly ───────────────────────────────

(deftest a-violating-set-settles-the-same-way-in-every-arrival-order
  ;; The whole reason for the change.  Today's assert path blames whichever assert
  ;; arrives last for a property of a *set*: state the separation first and the second
  ;; membership throws, state it last and the memberships are merely reported.  Under
  ;; arbitration every order lands on the same belief and the same dilemma.
  ;;
  ;; Run with the policy on, because that is the configuration in which all three
  ;; routes — the two memberships and the declaration — agree.  24 orderings.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(genl zdog thing) 'CxUniverse)
               #(v/assert % '(disjoint zdog zfish) 'CxUniverse)
               #(v/assert % '(zdog Rex) 'CxUniverse)
               #(v/assert % '(zfish Rex) 'CxUniverse)]
          observe (fn [kb]
                    {:dog        (boolean (seq (v/sentexes-matching kb '(zdog Rex) 'CxUniverse)))
                     :fish       (boolean (seq (v/sentexes-matching kb '(zfish Rex) 'CxUniverse)))
                     :dilemmas   (count (v/contradictions kb))
                     :conflicts  (count (v/conflicts kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "disjointness clash: " (count os) " distinct outcomes across 24 orderings — "
               (pr-str os)))
      (testing "and the one outcome represents the clash rather than hiding it"
        (is (= {:dog true :fish true :dilemmas 1 :conflicts 0} (first os))))
      (tu/clear-kb! (tu/test-kb)))))

(deftest a-clash-across-a-visibility-edge-settles-the-same-way-in-every-arrival-order
  ;; The clash only one side can see.  `CxZGen` is general and `CxZSpec` sees
  ;; it, so the two memberships are jointly visible from exactly one of the two contexts
  ;; they are written in — and the definitional checks are scoped to the asserting
  ;; context, correctly, because a context is only convicted on grounds it can see.
  ;; Asking the pair's question from the arriving sentex's *own* context therefore
  ;; answers it from the general side, which cannot see the specific membership at all.
  ;;
  ;; Belief is what has to agree, not storage: the general-claim-last order admits the
  ;; default and defeats it, while the specific-claim-last order is refused at the entry point
  ;; (admitting what the KB can never believe is still what `:arbitrate` will not do).
  ;; That is `belief-agrees-whichever-arrived-first-under-arbitrate`'s split, one
  ;; visibility edge out.  120 orderings.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(genlCx CxZGen CxUniverse) 'CxUniverse)
               #(v/assert % '(genlCx CxZSpec CxZGen) 'CxUniverse)
               #(v/assert % '(disjoint zoanimal zoplant) 'CxUniverse)
               #(v/assert % '(zoanimal OX) 'CxZGen {:strength :monotonic})
               #(v/assert % '(zoplant OX) 'CxZSpec)]
          observe (fn [kb]
                    {:known-true (v/ask? kb '(zoanimal OX) 'CxZGen)
                     :default    (v/ask? kb '(zoplant OX) 'CxZSpec)
                     :dilemmas   (count (v/contradictions kb))
                     :conflicts  (count (v/conflicts kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering]
                                  (try (op kb) (catch clojure.lang.ExceptionInfo _ nil)))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "clash across a visibility edge: " (count os)
               " distinct outcomes across 120 orderings — " (pr-str os)))
      (testing "and the one outcome defeats the default rather than leaving it beside content that denies it"
        (is (= {:known-true true :default false :dilemmas 0 :conflicts 0} (first os))))
      (tu/clear-kb! (tu/test-kb)))))

(deftest a-self-tuple-under-an-asymmetric-predicate-asserts-idempotently
  ;; `(P a a)` is its own converse, so once stored it answers its own probe: a second
  ;; assert of content the KB already believes convicted it against the copy the first
  ;; one left, and `assert` stopped deduping to the handle it already had.  Only at
  ;; `:monotonic`, since `refuses-assert?` reads the class — which is why the first
  ;; assert and every re-assert after it disagreed about the same sentence.
  ;;
  ;; Admitting it is the reading all three shipped surfaces state: `CxCore.txt`'s comment
  ;; on `asymmetric`, `docs/taxonomy.md` and `docs/inherit.md`.  Asymmetry does not hand
  ;; you irreflexivity, and a conviction needs a *believed opposing* claim.
  (let [kb (tu/fresh)]
    (v/assert kb '(binary_predicate zSelfLarger) 'CxUniverse)
    (v/assert kb '(asymmetric zSelfLarger) 'CxUniverse)
    (let [h1 (v/assert kb '(zSelfLarger zrock zrock) 'CxUniverse {:strength :monotonic})
          h2 (v/assert kb '(zSelfLarger zrock zrock) 'CxUniverse {:strength :monotonic})]
      (is (= h1 h2) "the re-assert dedups to the handle the first one minted")
      (is (v/ask? kb '(zSelfLarger zrock zrock) 'CxUniverse)))
    (testing "and the mirror pair it is not a case of still refuses"
      (v/assert kb '(zSelfLarger zbig zsmall) 'CxUniverse {:strength :monotonic})
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"cannot hold both ways"
           (v/assert kb '(zSelfLarger zsmall zbig) 'CxUniverse {:strength :monotonic}))))
    (testing "and a self tuple under a sub-predicate the mark descends to is the same case"
      (v/assert kb '(genl zSelfSmaller zSelfLarger) 'CxUniverse)
      (let [h1 (v/assert kb '(zSelfSmaller zpebble zpebble) 'CxUniverse {:strength :monotonic})
            h2 (v/assert kb '(zSelfSmaller zpebble zpebble) 'CxUniverse {:strength :monotonic})]
        (is (= h1 h2) "the descended mark convicts a pair, not a sentence against itself")))
    (tu/clear-kb! (tu/test-kb))))

(deftest an-asymmetric-violating-set-settles-the-same-way-in-every-arrival-order
  ;; the same invariant for the check that was silent rather than throwing: the
  ;; declaration may arrive before or after either direction of the relation
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(asymmetric zTypLarger) 'CxUniverse)
               #(v/assert % '(zTypLarger zdog zcat) 'CxUniverse)
               #(v/assert % '(zTypLarger zcat zdog) 'CxUniverse)]
          observe (fn [kb]
                    {:fwd      (v/ask? kb '(zTypLarger zdog zcat) 'CxUniverse)
                     :bwd      (v/ask? kb '(zTypLarger zcat zdog) 'CxUniverse)
                     :dilemmas (count (v/contradictions kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "asymmetric pair: " (count os) " distinct outcomes across 6 orderings — "
               (pr-str os)))
      (is (= {:fwd true :bwd true :dilemmas 1} (first os)))
      (tu/clear-kb! (tu/test-kb)))))

(deftest a-report-orders-its-sides-by-content-not-by-arrival
  ;; `clash-nogoods` orders the pair inside `:sentence` "by their printed form rather
  ;; than by which side was walked", and for a stated reason: a set that told the two
  ;; entries apart would report one clash or two depending on the arrival order.  The
  ;; report the caller actually reads has to follow the same rule, or the answer to
  ;; "which side is `(first (:sides c))`?" is whichever was asserted first — a handle
  ;; keyed on arrival order, reaching the public reading through the back entry point.
  (binding [checks/*arbitrate-constraints?* true]
    (let [shape (fn [ops]
                  (let [kb (tu/fresh)]
                    (doseq [op ops] (op kb))
                    (mapv (fn [r] [(:sentence r) (mapv :sentence (:sides r)) (:handles r)])
                          (v/contradictions kb))))
          strip (fn [rs] (mapv (fn [[s sides _]] [s sides]) rs))
          dog #(v/assert % '(zdog Rex) 'CxUniverse)
          cat #(v/assert % '(zcat Rex) 'CxUniverse)
          sep #(v/assert % '(disjoint zdog zcat) 'CxUniverse)
          pos #(v/assert % '(zbird Tweety) 'CxUniverse)
          neg #(v/assert % '(not (zbird Tweety)) 'CxUniverse)]
      (testing "a definitional clash"
        (is (= (strip (shape [sep dog cat])) (strip (shape [sep cat dog])))
            "the two sides swap places when the two memberships swap arrival order"))
      (testing "a plain rebuttal"
        (is (= (strip (shape [pos neg])) (strip (shape [neg pos])))))
      (testing "and `:handles` names the sides in the order `:sides` reports them"
        (let [[[_ sides handles]] (shape [sep dog cat])
              [[_ sides' handles']] (shape [sep cat dog])]
          (is (= sides sides'))
          (is (= 2 (count handles) (count handles')))))
      (tu/clear-kb! (tu/test-kb)))))

(deftest a-metatype-clique-settles-the-same-way-in-every-arrival-order
  ;; the same invariant for the trigger the taxonomy owns rather than the vocabulary:
  ;; the separation is a property of *four* sentences — the metatype declaration and the
  ;; two memberships that make the clique, plus the two type memberships that clash —
  ;; and none of them is the one to blame.  120 orderings.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(disjoint_metatype z_species) 'CxUniverse)
               #(v/assert % '(z_species zdog) 'CxUniverse)
               #(v/assert % '(z_species zcat) 'CxUniverse)
               #(v/assert % '(zdog Rex) 'CxUniverse)
               #(v/assert % '(zcat Rex) 'CxUniverse)]
          observe (fn [kb]
                    {:dog       (boolean (seq (v/sentexes-matching kb '(zdog Rex) 'CxUniverse)))
                     :cat       (boolean (seq (v/sentexes-matching kb '(zcat Rex) 'CxUniverse)))
                     :dilemmas  (count (v/contradictions kb))
                     :conflicts (count (v/conflicts kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "metatype clique: " (count os) " distinct outcomes across 120 orderings — "
               (pr-str os)))
      (is (= {:dog true :cat true :dilemmas 1 :conflicts 0} (first os)))
      (tu/clear-kb! (tu/test-kb)))))

;;; ── the policy as a per-KB option, not only a process default ──────────

;; `checks/*arbitrate-constraints?*` decides the policy for a whole process, and it is
;; set from an environment variable — so an application that wants one KB curating a
;; hand-written ontology beside one ingesting a corpus whose schema arrives last could
;; not have both.  `open-kb`'s `:constraints` is the same policy per KB, and it is a
;; entry-point setting for `:naming`'s reason: whether a *writer* is told no is a question
;; about the application.

(defn- arbitrating-kb [] (v/open-kb (assoc tu/scratch-space :constraints :arbitrate)))
(defn- refusing-kb    [] (v/open-kb (assoc tu/scratch-space :constraints :refuse)))

(deftest the-per-kb-policy-decides-in-both-directions
  (testing ":arbitrate admits under a process default that refuses"
    (tu/with-neutral-kb [kb arbitrating-kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse)
        (is (v/assert kb (list cat_t Muffet) 'CxUniverse))
        (is (= 1 (count (v/contradictions kb)))))))
  (testing ":refuse refuses under a process default that arbitrates"
    (binding [checks/*arbitrate-constraints?* true]
      (tu/with-neutral-kb [kb refusing-kb]
        (tu/with-terms [dog_t cat_t Muffet]
          (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
          (v/assert kb (list dog_t Muffet) 'CxUniverse)
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list cat_t Muffet) 'CxUniverse)))
          (is (nil? (v/handle-of kb (list cat_t Muffet) 'CxUniverse))))))))

(deftest a-kb-that-names-no-policy-still-reads-the-process-default
  ;; nil is not a third policy — it means the caller said nothing, and the var is what
  ;; answers then.  Without this, setting a default per KB would take the env var and
  ;; every `binding` out of the picture for every KB in the process.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (v/assert kb (list dog_t Muffet) 'CxUniverse)
        (is (v/assert kb (list cat_t Muffet) 'CxUniverse)
            "an unstated policy arbitrates when the process default does")))))

(deftest a-declaration-arriving-last-reaches-back-under-either-policy
  ;; A schema that arrives after the facts it convicts is the normal shape of an import.
  ;; It reaches back under both policies, because a recover of the same records decides the
  ;; pair from its region whatever the policy — a live KB that only filed the clash would
  ;; go on believing the weaker side until its first restart.  The policies differ at the
  ;; entry point, which the tests above cover, and not here.
  (doseq [[label build] [[":refuse" refusing-kb] [":arbitrate" arbitrating-kb]]]
    (testing label
      (tu/with-neutral-kb [kb build]
        (tu/with-terms [dog_t cat_t Muffet]
          (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list cat_t Muffet) 'CxUniverse)
          (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
          (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
          (is (not (v/ask? kb (list cat_t Muffet) 'CxUniverse))
              "the default loses to known-true content it was stored before")
          (is (not-any? #{:disjoint} (map :violation (v/violations kb)))
              "decided, so not also filed as exposed"))))))

(deftest belief-agrees-whichever-arrived-first-under-arbitrate
  ;; Storage does not: the schema-first order **refuses** the clashing membership at the
  ;; entry point (admitting what the KB can never believe is what `:arbitrate` still will not
  ;; do), while the facts-first order admits and defeats it.  What has to agree is
  ;; belief, and it does.
  (let [believed (fn [build ops]
                   (tu/with-neutral-kb [kb build]
                     (tu/with-terms [dog_t cat_t Muffet]
                       (doseq [op (ops dog_t cat_t Muffet)]
                         (try (op kb) (catch clojure.lang.ExceptionInfo _ nil)))
                       {:known-true (v/ask? kb (list dog_t Muffet) 'CxUniverse)
                        :default    (v/ask? kb (list cat_t Muffet) 'CxUniverse)})))
        facts-first  (believed arbitrating-kb
                               (fn [d c F] [#(v/assert % (list d F) 'CxUniverse {:strength :monotonic})
                                            #(v/assert % (list c F) 'CxUniverse)
                                            #(v/assert % (list 'disjoint d c) 'CxUniverse)]))
        schema-first (believed arbitrating-kb
                               (fn [d c F] [#(v/assert % (list 'disjoint d c) 'CxUniverse)
                                            #(v/assert % (list d F) 'CxUniverse {:strength :monotonic})
                                            #(v/assert % (list c F) 'CxUniverse)]))]
    (is (= facts-first schema-first))
    (is (= {:known-true true :default false} facts-first))))

(deftest an-unknown-constraints-policy-is-refused
  ;; the same failure `:naming` is held to: a KB that silently took `:refuse` when it was
  ;; told `:arbitrate` refuses content the caller expected to land and be arbitrated
  (let [d (try (v/open-kb (assoc tu/scratch-space :constraints :arbitrat)) nil
               (catch clojure.lang.ExceptionInfo e (ex-data e)))]
    (is (= :unknown-option (:type d)))
    (is (= [:arbitrate :refuse] (:options d)))))

(deftest a-restart-agrees-with-the-live-kb-under-either-policy
  ;; The policy lives on the KB handle, not in the store, so the same records can be
  ;; reopened under the other one — and a rebuild's region is *every* stored sentex, so
  ;; `clash-nogoods` finds a standing clash from the region alone and decides it whichever
  ;; policy is in force.  The live KB decides the same pair as the declaration arrives
  ;; (`settle/clash-candidates`), so belief is one answer either side of a restart.
  ;; Its own space, keyed by a namespaced vector rather than a number, so it can
  ;; collide with nothing — including a second concurrent run, which `VAELII_TEST_SPACE`
  ;; moves the suite's block for but could not move a hard-coded integer.
  (let [spaces {:space [::restart]}
        build! (fn [kb dog_t cat_t Muffet]
                 (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
                 (v/assert kb (list cat_t Muffet) 'CxUniverse)
                 (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse))
        believed (fn [kb dog_t cat_t Muffet]
                   [(v/in? kb (v/handle-of kb (list dog_t Muffet) 'CxUniverse))
                    (v/in? kb (v/handle-of kb (list cat_t Muffet) 'CxUniverse))])]
    (tu/with-terms [dog_t cat_t Muffet]
      (let [kb (doto (v/open-kb (assoc spaces :constraints :refuse :recover? false)) (tu/clear-kb!))]
        (try
          (build! kb dog_t cat_t Muffet)
          (is (= [true false] (believed kb dog_t cat_t Muffet))
              ":refuse decides the late declaration's clash as it arrives")
          (is (not-any? #{:disjoint} (map :violation (v/violations kb))))
          (testing "recovered under the same policy, the answer is the same"
            (let [re (v/open-kb (assoc spaces :constraints :refuse :recover? :auto))]
              (is (= [true false] (believed re dog_t cat_t Muffet)))))
          (testing "and under :arbitrate"
            (let [re (v/open-kb (assoc spaces :constraints :arbitrate :recover? :auto))]
              (is (= [true false] (believed re dog_t cat_t Muffet)))))
          (finally (tu/clear-kb! kb)))))))

