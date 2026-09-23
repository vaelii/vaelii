;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-support-test
  "Support-carrying path consistency: which stored sentexes an entailed relation rests on.

  A composed relation has no handle — nothing stored says `A` is inside `D`, the table
  does — so what an explanation can name, and what a justification would rest on, has to
  come out of the fixpoint itself.  Two halves are tested here: the engine's, over a toy
  algebra with handles standing in for sentexes, and the KB's, where the handles are real
  and retracting them is what proves the support sound."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.space :as space]
            [vaelii.test-util :as tu]))

;; ---- the engine, over a toy point algebra --------------------------------

(def ^:private universe #{:lt :eq :gt})

(def ^:private converse-rel {:lt :gt, :eq :eq, :gt :lt})

(def ^:private composition
  {:lt {:lt #{:lt}    :eq #{:lt}    :gt universe}
   :eq {:lt #{:lt}    :eq #{:eq}    :gt #{:gt}}
   :gt {:lt universe  :eq #{:gt}    :gt #{:gt}}})

(defn- compose-sets [s1 s2]
  (into #{} (mapcat (fn [a] (mapcat (fn [b] (get-in composition [a b])) s2))) s1))

(defn- converse-set [rels] (into #{} (map converse-rel) rels))

(def ^:private point-algebra
  {:universe universe :identity #{:eq} :compose compose-sets :converse converse-set})

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
        "nothing asserted A<C; composition pinned it")
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

(deftest the-support-pass-tightens-exactly-as-the-plain-one-does
  ;; the two share their step, and this is the contract that keeps them sharing it
  (let [[n s] (net ['A 'B #{:lt :eq} 1] ['B 'C #{:lt} 2] ['C 'D #{:lt} 3])]
    (is (= (qcn/path-consistent n '[A B C D] point-algebra)
           (:network (qcn/path-consistent-with-support n s '[A B C D] point-algebra))))))

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

(deftest support-is-not-tracked-unless-it-is-asked-for
  ;; `path-consistent` keeps its contract exactly: a network in, a network or
  ;; `:inconsistent` out, and no support map allocated on the way
  (let [[n _] (net ['A 'B #{:lt} 1] ['B 'C #{:lt} 2])]
    (is (map? (qcn/path-consistent n '[A B C] point-algebra)))
    (is (= #{:lt} (qcn/constraint (qcn/path-consistent n '[A B C] point-algebra)
                                  point-algebra 'A 'C)))))

;; ---- the KB, where the handles are real ----------------------------------

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxSpace "upper"] [CxTime "upper"]])
                        (v/add-prover (space/spatial-prover))
                        (v/add-prover (iv/allen-prover)))))

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
  ;; soundness, stated as the property rather than as a list: the support may
  ;; over-approximate, but it may never name something that is not a believed fact this
  ;; calculus read
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
          (is (v/in? kb h) (str "handle " h " is believed"))
          (is (contains? space/spatial-predicates (first (:sentence s)))
              (str "handle " h " is a fact of this calculus, not " (:sentence s))))))))

(tu/deftest-kb retracting-any-supporter-of-a-chain-destroys-the-entailment
  ;; the strongest thing a support claim can be asked for: take away any one link and the
  ;; conclusion goes.  (In general the set is an over-approximation, so only "all of it"
  ;; is guaranteed — a chain is the case where every member is genuinely necessary.)
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
  ;; A reaches E two ways.  Support propagates where a constraint *moves*, so the route
  ;; that got there first is the one named and the second re-derives a value already
  ;; reached — exactly what a justification is, one support list rather than all of them.
  ;; Retracting the named set therefore destroys *that* derivation, and asking again names
  ;; the survivor.
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
  ;; the negative half of the read carries support like the positive one
  (tu/with-terms [A B D]
    (let [h1 (v/assert kb (list 'nonTangentialProperPart A B) C)
          h2 (v/assert kb (list 'not (list 'regionConnectedTo B D)) C)]
      (is (= #{:dc} (space/possible-relations kb C A D)))
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
  ;; a separate cache from `tighten`'s, so asking for support twice runs the pass once and
  ;; an ordinary query pays for none of it.  The key is the network *and* the asserted
  ;; support, because the same sentences at different handles read into the same network.
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
    (let [net (space/region-network kb C)
          ns  (qkb/nodes net)
          plain (qcn/path-consistent net ns (:algebra space/rcc8))
          with  (qcn/path-consistent-with-support net (qkb/network-support kb space/rcc8 C)
                                                  ns (:algebra space/rcc8))]
      (is (= plain (:network with)))
      (is (set/subset? (set (keys (:support with))) (set (keys plain)))
          "support is recorded only for pairs the network actually constrains"))))
