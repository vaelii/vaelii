;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-support-test
  "Support-carrying path consistency, over a toy algebra with integers for handles and
  over a KB where retracting the handles tests the support."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.space :as space]
            [vaelii.qcn-test :refer [converse-set point-algebra universe]]
            [vaelii.test-util :as tu]))

;; ---- the engine, over `qcn_test`'s toy point algebra ---------------------

(defn- net
  "A network plus its asserted support, from `[i j rels handle]` entries — the form a
  reader produces."
  [& entries]
  (reduce (fn [[n s] [i j rels h]]
            [(assoc n [i j] rels [j i] (converse-set rels))
             (-> s (update [i j] (fnil conj #{}) h) (update [j i] (fnil conj #{}) h))])
          [{} {}]
          entries))

(deftest an-asserted-constraint-is-supported-by-its-own-handle
  (let [[n s] (net ['A 'B #{:lt} 1])
        r     (qcn/path-consistent-with-support n s '[A B] point-algebra)]
    (is (= #{1} (get (:support r) '[A B])))
    (is (= #{1} (get (:support r) '[B A])) "both directions, as both constraints are")))

(deftest a-composed-constraint-is-supported-by-both-its-inputs
  (let [[n s] (net ['A 'B #{:lt} 1] ['B 'C #{:lt} 2])
        r     (qcn/path-consistent-with-support n s '[A B C] point-algebra)]
    (is (= #{:lt} (qcn/constraint (:network r) point-algebra 'A 'C))
        "nothing asserted A<C; composition determined it")
    (is (= #{1 2} (get (:support r) '[A C])))
    (is (= #{1 2} (get (:support r) '[C A])))))

(deftest a-longer-chain-accumulates-every-link
  (let [[n s] (net ['A 'B #{:lt} 1] ['B 'C #{:lt} 2] ['C 'D #{:lt} 3] ['D 'E #{:lt} 4])
        r     (qcn/path-consistent-with-support n s '[A B C D E] point-algebra)]
    (is (= #{:lt} (qcn/constraint (:network r) point-algebra 'A 'E)))
    (is (= #{1 2 3 4} (get (:support r) '[A E]))
        "four compositions away, so every link is named")
    (is (= #{1 2} (get (:support r) '[A C])) "and a nearer pair names only what it used")))

(deftest an-unconstrained-pair-is-supported-by-nothing
  (let [[n s] (net ['A 'B #{:lt} 1] ['C 'D #{:lt} 2])
        r     (qcn/path-consistent-with-support n s '[A B C D] point-algebra)]
    (is (= universe (qcn/constraint (:network r) point-algebra 'A 'D)))
    (is (nil? (get (:support r) '[A D])) "there is nothing to support \"unknown\"")))

(deftest an-emptied-constraint-names-the-pair-and-its-culprits
  (testing "a cycle no order of the three can satisfy"
    (let [[n s] (net ['A 'B #{:lt} 1] ['B 'C #{:lt} 2] ['C 'A #{:lt} 3])
          r     (qcn/path-consistent-with-support n s '[A B C] point-algebra)]
      (is (:inconsistent r) "the pair that emptied is named")
      (is (= #{1 2 3} (:culprits r))
          "and all three constraints are behind it, whichever pair emptied first")))
  (testing "a constraint that arrives empty blames itself"
    (let [[n s] (net ['A 'B #{:lt} 1])
          n'    (assoc n '[X Y] #{} '[Y X] #{})
          s'    (assoc s '[X Y] #{7} '[Y X] #{7})
          r     (qcn/path-consistent-with-support n' s' '[A B X Y] point-algebra)]
      (is (= '[X Y] (:inconsistent r)))
      (is (= #{7} (:culprits r))))))

;; ---- the KB, where the handles are real ----------------------------------

(use-fixtures :once (tu/loaded #(doto % (tu/load-core!)
                                      (v/add-prover (space/spatial-prover))
                                      (v/add-prover (iv/allen-prover)))))
(use-fixtures :each (tu/neutral))

(def ^:private C 'CxUniverse)

(tu/deftest-kb an-asserted-relation-is-supported-by-its-own-sentex
  (tu/with-terms [A B]
    (let [h (v/assert kb (list 'nonTangentialProperPart A B) C)]
      (is (= #{h} (qkb/support space/rcc8 kb C A B)))
      (is (= #{h} (qkb/support space/rcc8 kb C B A))))))

(tu/deftest-kb a-two-step-composition-is-supported-by-both-sentexes
  (tu/with-terms [A B D]
    (let [h1 (v/assert kb (list 'nonTangentialProperPart A B) C)
          h2 (v/assert kb (list 'nonTangentialProperPart B D) C)]
      (is (nil? (v/handle-of kb (list 'nonTangentialProperPart A D) C))
          "nothing stored says A is inside D")
      (is (v/ask? kb (list 'nonTangentialProperPart A D) C) "but the network entails it")
      (is (= #{h1 h2} (qkb/support space/rcc8 kb C A D))))))

(tu/deftest-kb a-three-step-chain-reports-all-three
  (tu/with-terms [A B D E]
    (let [hs (mapv #(v/assert kb % C)
                   [(list 'nonTangentialProperPart A B)
                    (list 'nonTangentialProperPart B D)
                    (list 'nonTangentialProperPart D E)])]
      (is (v/ask? kb (list 'nonTangentialProperPart A E) C))
      (is (= (set hs) (qkb/support space/rcc8 kb C A E))))))

(tu/deftest-kb every-reported-handle-is-a-believed-sentex-of-the-calculus
  (tu/with-terms [A B D Other tmpLikes]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (v/assert kb (list tmpLikes A Other) C)                 ; a fact of no calculus
    (v/assert kb (list 'before A B) C)                      ; a fact of another one
    (let [sup (qkb/support space/rcc8 kb C A D)]
      (is (seq sup))
      (doseq [h sup]
        (let [s (v/sentex kb h)]
          (is (some? s) (str "handle " h " names a stored sentex"))
          (is (v/believed? kb h) (str "handle " h " is believed"))
          (is (contains? space/spatial-predicates (first (:sentence s)))
              (str "handle " h " is a fact of this calculus, not " (:sentence s))))))))

(tu/deftest-kb retracting-any-supporter-of-a-chain-destroys-the-entailment
  ;; a chain, because there every member of the support is necessary
  (tu/with-terms [A B D E]
    (let [links [(list 'nonTangentialProperPart A B)
                 (list 'nonTangentialProperPart B D)
                 (list 'nonTangentialProperPart D E)]]
      (doseq [dropped (range 3)]
        (let [hs (mapv #(v/assert kb % C) links)]
          (is (= (set hs) (qkb/support space/rcc8 kb C A E)))
          (v/retract! kb (nth hs dropped))
          (is (not (v/ask? kb (list 'nonTangentialProperPart A E) C))
              (str "dropping link " dropped " breaks the chain"))
          (is (empty? (qkb/support space/rcc8 kb C A E))
              "and the pair it entailed is unconstrained again")
          (doseq [h hs :when (not= h (nth hs dropped))] (v/retract! kb h)))))))

(tu/deftest-kb the-support-is-one-witness-not-every-witness
  ;; A reaches E two ways
  (tu/with-terms [A B D E]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B E) C)
    (v/assert kb (list 'nonTangentialProperPart A D) C)
    (v/assert kb (list 'nonTangentialProperPart D E) C)
    (is (v/ask? kb (list 'nonTangentialProperPart A E) C))
    (let [sup (qkb/support space/rcc8 kb C A E)]
      (is (= 2 (count sup)) "one route, not the union of both")
      (testing "that route away, the other still entails it — and now it is what answers"
        (doseq [h sup] (v/retract! kb h))
        (is (v/ask? kb (list 'nonTangentialProperPart A E) C))
        (let [sup' (qkb/support space/rcc8 kb C A E)]
          (is (= 2 (count sup')))
          (is (empty? (set/intersection sup sup')) "a different pair of handles")
          (testing "and taking the survivor away leaves nothing to entail it"
            (doseq [h sup'] (v/retract! kb h))
            (is (not (v/ask? kb (list 'nonTangentialProperPart A E) C)))))))))

(tu/deftest-kb a-negative-fact-supports-what-it-narrows
  (tu/with-terms [A B D]
    (let [h1 (v/assert kb (list 'nonTangentialProperPart A B) C)
          h2 (v/assert kb (list 'not (list 'regionConnectedTo B D)) C)]
      (is (= #{:dc} (qkb/possible space/rcc8 kb C A D)))
      (is (= #{h1 h2} (qkb/support space/rcc8 kb C A D))))))

(tu/deftest-kb an-inconsistent-network-reports-the-culprit-pair-and-its-support
  (tu/with-terms [A B D]
    (let [hs (mapv #(v/assert kb % C)
                   [(list 'before A B) (list 'before B D) (list 'after A D)])
          r  (qkb/inconsistency-culprits iv/allen kb C)]
      (is (some? r) "the network is unsatisfiable and says which pair emptied")
      (is (vector? (:pair r)))
      (is (= (set hs) (:support r))
          "and all three facts are behind it — no two of them clash")
      (testing "a satisfiable network reports no culprits at all"
        (v/retract! kb (nth hs 2))
        (is (nil? (qkb/inconsistency-culprits iv/allen kb C))))
      (testing "and support of an entailment is empty while the network is impossible"
        (v/assert kb (list 'after A D) C)
        (is (empty? (qkb/support iv/allen kb C A D)))))))

(tu/deftest-kb the-support-pass-is-memoized-on-the-network-and-its-support
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'nonTangentialProperPart B D) C)
    (let [cache (:support-cache space/rcc8)]
      (reset! cache {})
      (qkb/support space/rcc8 kb C A D)
      (is (= 1 (count @cache)))
      (let [snapshot @cache]
        (qkb/support space/rcc8 kb C A B)
        (is (identical? snapshot @cache) "the second read is a cache hit"))
      (testing "and a change of belief is a different network, so a different key"
        (v/assert kb (list 'nonTangentialProperPart A D) C)
        (qkb/support space/rcc8 kb C A D)
        (is (= 2 (count @cache))))
      (reset! cache {}))))

(tu/deftest-kb the-support-network-agrees-with-the-plain-pass
  (tu/with-terms [A B D]
    (v/assert kb (list 'nonTangentialProperPart A B) C)
    (v/assert kb (list 'tangentialProperPart B D) C)
    (let [net (qkb/network kb space/rcc8 C)
          ns  (qkb/nodes net)
          plain (qcn/path-consistent net ns (:algebra space/rcc8))
          with  (qcn/path-consistent-with-support net (qkb/network-support kb space/rcc8 C)
                                                  ns (:algebra space/rcc8))]
      (is (= plain (:network with)))
      (is (set/subset? (set (keys (:support with))) (set (keys plain)))
          "support is recorded only for pairs the network actually constrains"))))
