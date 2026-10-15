;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.space-test
  "RCC-8 (`vaelii.impl.space`), and the claims the four spatial calculi share, as tables
  with one row per calculus."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.distance :as dist]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.orientation :as dir]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.relative :as rel]
            [vaelii.impl.space :as space]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core!)
                        (v/add-reasoner :rcc8 :cardinal :relative :distance))))

(def ^:private C 'CxUniverse)

(def ^:private calculi
  {:rcc8 space/rcc8, :cardinal dir/cardinal, :relative rel/relative,
   :distance dist/qualitative-distance})

(defn- fill
  "`form` with the placeholders `$a` and `$b` replaced by the row's terms."
  [form a b]
  (walk/postwalk-replace {'$a a '$b b} form))

(tu/deftest-kb composition-derives-an-unasserted-base-relation
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "NTPP∘NTPP = NTPP"
      (is (v/ask? kb (list 'nonTangentialProperPart A D) C)))
    (testing "and the table pins the pair to that one relation"
      (is (= #{:ntpp} (qkb/possible space/rcc8 kb C A D)))
      (is (= :ntpp (qkb/definite space/rcc8 kb C A D))))
    (testing "so a base relation the network excludes is not answered"
      (is (not (v/ask? kb (list 'spatiallyDisconnected A D) C)))
      (is (not (v/ask? kb (list 'externallyConnected A D) C)))
      (is (not (v/ask? kb (list 'tangentialProperPart A D) C))))
    (testing "the converse direction is derived with it"
      (is (v/ask? kb (list 'nonTangentialProperPartInverse D A) C)))))

(tu/deftest-kb an-asserted-relation-answers-itself
  (tu/with-terms [A B]
    (v/assert kb (list 'externallyConnected A B) C)
    (is (v/ask? kb (list 'externallyConnected A B) C))
    (testing "and its converse, since EC is symmetric"
      (is (v/ask? kb (list 'externallyConnected B A) C)))
    (testing "while the relations it rules out are not entailed"
      (is (not (v/ask? kb (list 'spatiallyDisconnected A B) C)))
      (is (not (v/ask? kb (list 'partiallyOverlapping A B) C)))
      (is (not (v/ask? kb (list 'spatiallyEqual A B) C))))))

(tu/deftest-kb a-disjunctive-chain-leaves-the-pair-open
  (tu/with-terms [A B D]
    ;; DC∘DC is the whole universe
    (v/assert kb (list 'spatiallyDisconnected A B) C)
    (v/assert kb (list 'spatiallyDisconnected B D) C)
    (is (= space/all-relations (qkb/possible space/rcc8 kb C A D)))
    (is (= :unknown (qkb/definite space/rcc8 kb C A D)))
    (testing "an open pair entails no spatial predicate, not even a wide derived one"
      (is (not (v/ask? kb (list 'spatiallyDisconnected A D) C)))
      (is (not (v/ask? kb (list 'regionConnectedTo A D) C)))
      (is (not (v/ask? kb (list 'regionOverlaps A D) C))))))

(tu/deftest-kb a-derived-predicate-is-entailed-by-denotation-subset
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "#{:ntpp} sits inside every denotation that contains NTPP"
      (is (v/ask? kb (list 'partOfRegion A D) C))
      (is (v/ask? kb (list 'properPartOfRegion A D) C))
      (is (v/ask? kb (list 'regionOverlaps A D) C))
      (is (v/ask? kb (list 'regionConnectedTo A D) C)))
    (testing "and outside the denotations that do not"
      (is (not (v/ask? kb (list 'regionDiscreteFrom A D) C)))
      (is (not (v/ask? kb (list 'hasRegionPart A D) C))))
    (testing "the converse derived predicate holds the other way round"
      (is (v/ask? kb (list 'hasRegionPart D A) C))
      (is (not (v/ask? kb (list 'partOfRegion D A) C))))))

(tu/deftest-kb an-entailed-region-part-answers-generic-parthood
  ;; partOfRegion is below partOf and properPartOfRegion below properPartOf, so a region
  ;; part the network entails is a parthood tuple too
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "ground"
      (is (v/ask? kb (list 'partOf A D) C))
      (is (v/ask? kb (list 'properPartOf A D) C))
      (is (not (v/ask? kb (list 'properPartOf D A) C))))
    (testing "open"
      (is (= #{A B D} (set (map #(get % '?x) (v/ask kb (list 'partOf '?x D) C)))))
      (is (= #{B D} (set (map #(get % '?y) (v/ask kb (list 'properPartOf A '?y) C))))))))

(tu/deftest-kb the-calculus-entails-the-inert-partOf-edges-space-txt-states
  ;; space.txt states (genl spatiallyEqual partOfRegion) and three genlInverse edges to
  ;; partOf under set/inert. The calculus answers each edge's conclusion on its own.
  (doseq [[stated p goals]
          [['(genl spatiallyEqual partOfRegion) 'spatiallyEqual
            ['(partOfRegion $a $b) '(partOf $a $b)]]
           ['(genlInverse hasRegionPart partOf) 'hasRegionPart ['(partOf $b $a)]]
           ['(genlInverse tangentialProperPartInverse partOf) 'tangentialProperPartInverse
            ['(partOf $b $a)]]
           ['(genlInverse nonTangentialProperPartInverse partOf)
            'nonTangentialProperPartInverse ['(partOf $b $a)]]]]
    (testing (str stated)
      (let [h (v/handle-of kb stated C)]
        (is (integer? h) "the edge is stored")
        (is (false? (v/in? kb h)) "and is not believed"))
      (tu/with-terms [A B]
        (v/assert kb (list p A B) C)
        (doseq [g goals]
          (is (v/ask? kb (fill g A B) C) (str (fill g A B))))))))

(tu/deftest-kb a-region-cannot-stand-apart-from-itself
  (tu/with-terms [A B]
    ;; DC is its own converse, so the diagonal constraint is #{:dc}, non-empty, and
    ;; composition never narrows the diagonal: only the up-front check reports it
    (v/assert kb (list 'spatiallyDisconnected A A) C)
    (is (= :inconsistent (qkb/definite space/rcc8 kb C A B)))
    (is (not (v/ask? kb (list 'spatiallyDisconnected A A) C)))
    (testing "retracting it makes the network coherent again"
      (v/retract! kb (v/handle-of kb (list 'spatiallyDisconnected A A) C))
      (is (v/ask? kb (list 'partOfRegion A A) C)))))

(tu/deftest-kb a-reflexive-self-assertion-is-fine
  (tu/with-terms [A]
    (v/assert kb (list 'regionOverlaps A A) C)
    (is (= #{:eq} (qkb/possible space/rcc8 kb C A A)))
    (is (v/ask? kb (list 'partOfRegion A A) C))
    (is (v/ask? kb (list 'spatiallyEqual A A) C))
    (is (not (v/ask? kb (list 'properPartOfRegion A A) C)))))

(tu/deftest-kb an-open-argument-enumerates-the-entailed-regions
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "(partOfRegion A ?y), A itself included because P is reflexive"
      (is (= #{A B D} (set (map #(get % '?y) (v/ask kb (list 'partOfRegion A '?y) C))))))
    (testing "(partOfRegion ?x D)"
      (is (= #{A B D} (set (map #(get % '?x) (v/ask kb (list 'partOfRegion '?x D) C))))))
    (testing "a base relation enumerates only the pairs it is pinned to"
      (is (= #{B D}
             (set (map #(get % '?y) (v/ask kb (list 'nonTangentialProperPart A '?y) C))))))
    (testing "both arguments open enumerates the entailed pairs, off the diagonal"
      (is (= #{[A B] [A D] [B D]}
             (set (map (juxt #(get % '?x) #(get % '?y))
                       (v/ask kb (list 'properPartOfRegion '?x '?y) C))))))))

(tu/deftest-kb regions-of-a-mathematical-space-compose-like-any-other
  ;; three nested squares of an abstract plane: located in that plane, at no time
  (tu/with-terms [A B D]
    (doseq [r [A B D]]
      (v/assert kb (list 'spatial r) C)
      (v/assert kb (list 'atemporal r) C))
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (testing "the facts are admitted and believed, with no clash with atemporal"
      (is (empty? (v/contradictions kb)))
      (is (empty? (v/conflicts kb)))
      (is (v/ask? kb (list 'nonTangentialProperPart A B) C))
      (is (v/ask? kb (list 'nonTangentialProperPart B D) C)))
    (testing "the chain composes"
      (is (v/ask? kb (list 'nonTangentialProperPart A D) C)))
    (testing "and nothing concludes the squares are located in time"
      (doseq [r [A B D]]
        (is (not (v/ask? kb (list 'spatiotemporal r) C)))
        (is (not (v/ask? kb (list 'temporal r) C)))))))

(deftest the-registered-calculus-list-follows-the-registry
  ;; `registered-calculi` holds one memo entry keyed on the registry's identity, and a
  ;; registration swaps the atom.  Read off bare `{:provers atom}` maps, since a second KB
  ;; would clear the scratch space under the fixture.
  (let [registered {:provers (atom [(space/spatial-prover)])}
        bare       {:provers (atom [])}]
    (testing "a registry with no calculus prover claims nothing"
      (is (= [] (qkb/registered-calculi bare)))
      (is (nil? (qkb/calculus-for bare 'nonTangentialProperPart))))
    (testing "and one that registered the prover claims its calculus"
      (is (= [space/rcc8] (qkb/registered-calculi registered)))
      (is (= space/rcc8 (qkb/calculus-for registered 'nonTangentialProperPart))))
    (testing "asking about either afterwards still answers about that one"
      (is (= [] (qkb/registered-calculi bare)))
      (is (= [space/rcc8] (qkb/registered-calculi registered))))
    (testing "and a registration on a registry already asked about is picked up"
      (swap! (:provers bare) conj (space/spatial-prover))
      (is (= [space/rcc8] (qkb/registered-calculi bare))))))

(tu/deftest-kb the-four-calculi-share-no-predicate-and-type-every-argument-spatial
  (let [preds (map (comp set :predicates) (vals calculi))]
    (is (= 50 (count (apply set/union preds))))
    (is (= 50 (reduce + (map count preds))) "no predicate is claimed by two calculi")
    (is (= [] (remove #(and (v/ask? kb (list 'binary_predicate %) C)
                            (v/ask? kb (list 'arg % 1 'spatial) C)
                            (v/ask? kb (list 'arg % 2 'spatial) C))
                      (sort (apply set/union preds)))))))

(tu/deftest-kb a-spatial-relation-between-predicates-is-stored-or-refused-by-the-reading
  ;; temporary predicates, each a monotonic binary_predicate as genl is in CxUniverse
  (tu/with-terms [rel1 rel2]
    (doseq [r [rel1 rel2]] (v/assert kb (list 'binary_predicate r) C {:strength :monotonic}))
    (let [s (list 'northOf rel1 rel2)]
      (testing "entailing: the fact is stored, and the monotonic memberships defeat the spatial mints"
        (tu/with-entailing
          (let [h (v/assert kb s C)]
            (is (v/ask? kb s C))
            (doseq [r [rel1 rel2]]
              (is (some? (v/handle-of kb (list 'spatial r) C)) (str r))
              (is (not (v/ask? kb (list 'spatial r) C)) (str r)))
            (v/retract! kb h))))
      (testing "constraint-only: the assert is refused"
        (tu/without-entailing
         (is (= :arg-type (try (v/assert kb s C) nil
                               (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))))))

(deftest every-calculus-prover-ships-opt-in
  ;; the calculi share one prover record, so opt-in is asked by calculus, not by class
  (doseq [nm (keys calculi)]
    (is (not-any? #(qkb/prover-for? nm %) provers/default-provers) (name nm))))

(def ^:private stated-converses
  "The `(inverse P Q)` pairs space.txt states under `set/inert`, each as `[P Q]`."
  (vec (for [s (text/read-forms (io/file "resources/kb/upper/space.txt"))
             :when (and (seq? s) (= 'set/inert (first s))
                        (seq? (second s)) (= 'inverse (first (second s))))]
         (vec (rest (second s))))))

(deftest space-txt-states-every-converse-pair-of-the-calculi
  ;; The calculi are the source of truth: two distinct predicates of one calculus are a
  ;; converse pair when the algebra's converse of one's base relations is the other's.
  ;; Distance is symmetric, so it contributes no pair.
  (let [computed (set (for [calc   (vals calculi)
                            :let   [den  (:denotation calc)
                                    conv (:converse (:algebra calc))]
                            [p ps] den
                            [q qs] den
                            :when  (and (not= p q) (= (conv ps) qs))]
                        #{p q}))]
    (is (= 15 (count stated-converses)))
    (is (= computed (set (map set stated-converses)))
        "space.txt states exactly the converse pairs the algebras compute")))

(tu/deftest-kb an-inert-converse-fact-leaves-the-calculus-prover-answering-alone
  (doseq [[p q] stated-converses]
    (testing (str p " / " q)
      (let [h (v/handle-of kb (list 'inverse p q) C)]
        (is (integer? h) "the converse fact is stored")
        (is (false? (v/in? kb h)) "and is not believed"))
      (tu/with-terms [A B]
        (v/assert kb (list p A B) C)
        (let [goal (list p A B)
              calc (qkb/calculus-for kb p)
              appl (provers/applicable-provers kb (provers/registry kb) goal C)]
          (is (empty? (provers/shadowing-channels kb goal C)))
          (is (qkb/prover-for? (:name calc) (provers/sole-prover kb appl goal C))
              "the calculus prover answers the goal alone")
          (is (v/ask? kb (list q B A) C) "and the calculus answers the converse"))))))

(tu/deftest-kb a-believed-inverse-of-a-spatial-predicate-shadows-its-prover
  ;; The contrast the test above needs: the same goal, once a believed inverse names
  ;; partOfRegion, is no longer the calculus prover's alone.
  (tu/with-terms [A B containsRegion]
    (v/assert kb (list 'partOfRegion A B) C)
    (let [goal (list 'partOfRegion A B)
          h    (v/assert kb (list 'inverse 'partOfRegion containsRegion) C)
          appl (provers/applicable-provers kb (provers/registry kb) goal C)]
      (is (contains? (provers/shadowing-channels kb goal C) :inverse))
      (is (nil? (provers/sole-prover kb appl goal C)))
      (v/retract! kb h))))

(tu/deftest-kb without-the-prover-the-facts-are-inert
  ;; the same KB, read through the default registry, isolates what registering adds
  (doseq [[nm ab bd composed derived]
          [[:rcc8 'nonTangentialProperPart 'nonTangentialProperPart 'nonTangentialProperPart
            'partOfRegion]
           [:cardinal 'northeastOf 'northeastOf 'northeastOf 'northwardOf]
           [:relative 'leftOf 'leftOf 'leftOf 'leftwardOf]
           [:distance 'coLocatedWith 'closeTo 'closeTo 'withinNearDistanceOf]]]
    (testing (name nm)
      (tu/with-terms [A B D]
        (v/assert kb (list ab A B) C)
        (v/assert kb (list bd B D) C)
        (is (seq (provers/solve-goal-with kb provers/default-provers (list ab A B) C))
            "an asserted relation is retrievable as an ordinary fact")
        (is (empty? (provers/solve-goal-with kb provers/default-provers (list composed A D) C)))
        (is (empty? (provers/solve-goal-with kb provers/default-provers (list derived A D) C)))
        (is (v/ask? kb (list composed A D) C) "the registered prover composes them")
        (is (v/ask? kb (list derived A D) C))))))

(tu/deftest-kb the-network-follows-belief-and-visibility
  (doseq [[nm ab bd ad] [[:rcc8 'nonTangentialProperPart 'nonTangentialProperPart
                          'nonTangentialProperPart]
                         [:cardinal 'northeastOf 'northeastOf 'northeastOf]
                         [:relative 'leftOf 'leftOf 'leftOf]
                         [:distance 'coLocatedWith 'closeTo 'closeTo]]]
    (testing (name nm)
      (tu/with-terms [A B D CxInner CxOuter]
        (v/assert kb (list 'genlCx CxInner CxOuter) C)
        (v/assert kb (list ab A B) CxOuter)
        (v/assert kb (list bd B D) CxInner)
        (is (v/ask? kb (list ad A D) CxInner) "the inner context sees both facts")
        (is (not (v/ask? kb (list ad A D) CxOuter)) "the outer context sees only its own")
        (is (v/ask? kb (list ab A B) CxOuter))
        (v/retract! kb (v/handle-of kb (list bd B D) CxInner))
        (is (not (v/ask? kb (list ad A D) CxInner)) "retracting a link breaks the chain")))))

(tu/deftest-kb a-contradictory-network-answers-nothing
  (doseq [[nm p q derived identity]
          [[:rcc8 'spatiallyDisconnected 'spatiallyEqual 'partOfRegion 'partOfRegion]
           [:cardinal 'northOf 'southOf 'northwardOf 'sameLocationAs]
           [:relative 'leftOf 'rightOf 'leftwardOf 'sameRelativePositionAs]
           [:distance 'closeTo 'farFrom 'withinNearDistanceOf 'coLocatedWith]]]
    (testing (name nm)
      (tu/with-terms [A B D]
        (v/assert kb (list p A B) C)
        (v/assert kb (list q A B) C)
        (is (= #{} (qkb/possible (calculi nm) kb C A B)) "two disjoint base relations")
        (is (= :inconsistent (qkb/definite (calculi nm) kb C A B)))
        (is (qkb/inconsistent? (calculi nm) kb C))
        (is (not (v/ask? kb (list p A B) C)))
        (is (not (v/ask? kb (list q A B) C)))
        (is (not (v/ask? kb (list derived A B) C)))
        (is (empty? (v/ask kb (list derived A '?y) C)))
        (is (not (v/ask? kb (list identity D D) C)) "not even the diagonal")
        (v/retract! kb (v/handle-of kb (list q A B) C))
        (is (v/ask? kb (list p A B) C) "retracting one gives the other its answers back")
        (is (not (v/ask? kb (list q A B) C)))))))

(tu/deftest-kb an-inconsistency-derived-through-a-chain-is-caught
  (doseq [[nm link clash] [[:rcc8 'nonTangentialProperPart 'spatiallyDisconnected]
                           [:cardinal 'northOf 'southOf]
                           [:relative 'leftOf 'rightOf]]]
    (testing (name nm)
      (tu/with-terms [A B D]
        (v/assert kb (list link A B) C)
        (v/assert kb (list link B D) C)
        (v/assert kb (list clash A D) C)
        (is (= :inconsistent (qkb/definite (calculi nm) kb C A D)))
        (is (not (v/ask? kb (list link A B) C)) "no pair of the network is answered")))))

(tu/deftest-kb one-variable-twice-is-the-diagonal
  (doseq [[nm fact reflexive irreflexive]
          [[:rcc8 'nonTangentialProperPart 'partOfRegion ['properPartOfRegion]]
           [:cardinal 'northeastOf 'sameLocationAs ['northOf 'northwardOf]]
           [:relative 'leftOf 'sameRelativePositionAs ['leftOf 'leftwardOf]]
           [:distance 'farFrom 'coLocatedWith ['atSomeDistanceFrom 'farFrom]]]]
    (testing (name nm)
      (tu/with-terms [A B]
        (v/assert kb (list fact A B) C)
        (is (= #{A B} (set (map #(get % '?x) (v/ask kb (list reflexive '?x '?x) C))))
            "a predicate whose denotation holds the identity holds of every node")
        (doseq [p irreflexive]
          (is (empty? (v/ask kb (list p '?x '?x) C)) (str p " holds of none")))))))

(tu/deftest-kb two-facts-about-one-pair-intersect
  (doseq [[nm p q possible entailed refused]
          [[:rcc8 'partOfRegion 'properPartOfRegion #{:tpp :ntpp} [] ['spatiallyEqual]]
           [:cardinal 'northwardOf 'eastwardOf #{:ne} ['northeastOf] ['northOf]]
           [:relative 'leftwardOf 'frontwardOf #{:front-left} ['frontLeftOf] ['leftOf]]
           [:distance 'withinNearDistanceOf 'atSomeDistanceFrom #{:very-close :close :near}
            ['withinNearDistanceOf 'atSomeDistanceFrom] ['closeTo]]]]
    (testing (name nm)
      (tu/with-terms [A B]
        (v/assert kb (list p A B) C)
        (v/assert kb (list q A B) C)
        (is (= possible (qkb/possible (calculi nm) kb C A B)))
        (doseq [e entailed] (is (v/ask? kb (list e A B) C) (str e)))
        (doseq [r refused] (is (not (v/ask? kb (list r A B) C)) (str r)))))))

(tu/deftest-kb a-derived-assertion-constrains-without-pinning
  (doseq [[nm p possible entailed refused]
          [[:rcc8 'properPartOfRegion #{:tpp :ntpp}
            '[(partOfRegion $a $b) (regionOverlaps $a $b)]
            '[tangentialProperPart nonTangentialProperPart]]
           [:cardinal 'northwardOf #{:n :ne :nw}
            '[(northwardOf $a $b) (southwardOf $b $a)]
            '[northOf northeastOf northwestOf]]
           [:relative 'leftwardOf #{:left :front-left :behind-left}
            '[(leftwardOf $a $b) (rightwardOf $b $a)]
            '[leftOf frontLeftOf behindLeftOf]]
           [:distance 'withinNearDistanceOf #{:co :very-close :close :near}
            '[(withinNearDistanceOf $a $b)]
            '[coLocatedWith nearTo atSomeDistanceFrom]]]]
    (testing (name nm)
      (tu/with-terms [A B]
        (v/assert kb (list p A B) C)
        (is (= possible (qkb/possible (calculi nm) kb C A B)))
        (doseq [e entailed] (is (v/ask? kb (fill e A B) C) (str e)))
        (doseq [r refused]
          (is (not (v/ask? kb (list r A B) C)) (str r " is one of the relations left open")))))))
