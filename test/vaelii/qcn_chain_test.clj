;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-chain-test
  "Forward chaining on an entailed qualitative relation: the conclusion arrives, `why`
  names the facts the entailment rests on, and retracting one of them withdraws it."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.space :as space]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defmacro ^:private with-spatial
  "Run `body` with the RCC-8 prover registered.  `tu/neutral` restores the registry after
  the test."
  [kb & body]
  `(do (v/add-prover ~kb (space/spatial-prover)) ~@body))

(defn- nest!
  "Assert a containment chain, returning the handles in order."
  [kb ctx regions]
  (mapv (fn [[a b]]
          (v/assert kb (list 'nonTangentialProperPart a b) ctx {:strength :monotonic}))
        (partition 2 1 regions)))

;; ---- an entailment fires a rule ------------------------------------------

(tu/deftest-kb an-entailed-relation-fires-a-forward-rule
  (tu/with-terms [RegA RegB RegC contained CxChainSpace]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxChainSpace 'CxWell) 'CxUniverse
                {:strength :monotonic})
      (v/assert kb (list 'arg contained 1 'thing) 'CxUniverse {:strength :monotonic})
      ;; a rule over a DERIVED spatial predicate: partOfRegion denotes a disjunction, so
      ;; nothing stores it — it is only ever entailed
      (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list contained '?x)
                     CxChainSpace {:direction :forward})
      (nest! kb CxChainSpace [RegA RegB RegC])
      (testing "the transitive relation is entailed and genuinely not stored"
        (is (nil? (v/handle-of kb (list 'properPartOfRegion RegA RegC) CxChainSpace)))
        (is (= #{:ntpp} (v/possible-relations kb :rcc8 CxChainSpace RegA RegC))))
      (testing "and the rule fired on it"
        (is (seq (v/sentexes-matching kb (list contained RegA) '?ctx))
            "A is contained — from the asserted step")
        (is (seq (v/sentexes-matching kb (list contained RegB) '?ctx))
            "B is contained — B is a proper part of C")))))

(tu/deftest-kb the-conclusion-names-the-facts-the-entailment-rests-on
  (tu/with-terms [RegA RegB RegC deepIn CxChainWhy]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxChainWhy 'CxWell) 'CxUniverse
                {:strength :monotonic})
      (v/assert kb (list 'arg deepIn 1 'thing) 'CxUniverse {:strength :monotonic})
      ;; the antecedent binds A to C specifically, so the only way to satisfy it is the
      ;; two-step entailment
      (v/assert-rule kb [(list 'properPartOfRegion RegA RegC)] (list deepIn RegA)
                     CxChainWhy {:direction :forward})
      (let [[h-ab h-bc] (nest! kb CxChainWhy [RegA RegB RegC])
            ;; `sentexes-matching` promises the set and no order, so the count is asked
            ;; first: one placement, and `?ctx` sees exactly it
            concl (tu/sole-answer (v/sentexes-matching kb (list deepIn RegA) '?ctx)
                                  (list deepIn RegA))
            h     (:id concl)]
        (is (some? h) "the conclusion arrived")
        (testing "why names both stored steps — the support the network reported"
          (let [named (set (keys (:nodes (v/why kb h))))]
            (is (contains? named h-ab) "the A-B fact is in the proof")
            (is (contains? named h-bc) "the B-C fact is in the proof")))
        (testing "and it is derived, not a premise"
          (is (false? (v/premise? kb h))))))))

(tu/deftest-kb retracting-any-supporting-fact-withdraws-the-conclusion
  (tu/with-terms [RegA RegB RegC deepIn CxRetractSpace]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxRetractSpace 'CxWell) 'CxUniverse
                {:strength :monotonic})
      (v/assert kb (list 'arg deepIn 1 'thing) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list 'properPartOfRegion RegA RegC)] (list deepIn RegA)
                     CxRetractSpace {:direction :forward})
      (let [[_ h-bc] (nest! kb CxRetractSpace [RegA RegB RegC])]
        (is (seq (v/sentexes-matching kb (list deepIn RegA) '?ctx)) "believed while both steps stand")
        (testing "dropping the second step breaks the chain, and the conclusion goes"
          (v/retract! kb h-bc)
          (is (empty? (v/sentexes-matching kb (list deepIn RegA) '?ctx))
              "the entailment is gone, so what rested on it is gone")
          (is (= 8 (count (v/possible-relations kb :rcc8 CxRetractSpace RegA RegC)))
              "unconstrained is the whole universe — `#{}` would mean *inconsistent*"))
        (testing "and re-asserting it brings the conclusion back"
          (v/assert kb (list 'nonTangentialProperPart RegB RegC) CxRetractSpace
                    {:strength :monotonic})
          (is (seq (v/sentexes-matching kb (list deepIn RegA) '?ctx))
              "re-derived, at a fresh handle"))))))

;; ---- the boundaries ------------------------------------------------------

(tu/deftest-kb without-the-prover-registered-nothing-changes
  (tu/with-terms [RegA RegB RegC contained CxInertSpace]
    (v/assert kb (list 'genlCx CxInertSpace 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (v/assert kb (list 'arg contained 1 'thing) 'CxUniverse {:strength :monotonic})
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list contained '?x)
                   CxInertSpace {:direction :forward})
    (nest! kb CxInertSpace [RegA RegB RegC])
    (testing "the vocabulary loads, the facts store, and the rule simply does not fire —
              registering a prover is the opt-in, and this is the KB that never did"
      (is (empty? (v/sentexes-matching kb (list contained RegA) '?ctx)))
      (is (empty? (v/sentexes-matching kb (list contained RegB) '?ctx))))))

(tu/deftest-kb an-asserted-relation-still-fires-as-it-always-did
  (tu/with-terms [RegA RegB touching CxAssertedSpace]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxAssertedSpace 'CxWell) 'CxUniverse
                {:strength :monotonic})
      (v/assert kb (list 'arg touching 1 'thing) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list 'externallyConnected '?x '?y)] (list touching '?x)
                     CxAssertedSpace {:direction :forward})
      (v/assert kb (list 'externallyConnected RegA RegB) CxAssertedSpace
                {:strength :monotonic})
      (testing "the ordinary matched route is untouched — entailment is a union with it,
                never a replacement, so nothing that fired before stops firing"
        (is (seq (v/sentexes-matching kb (list touching RegA) '?ctx)))))))

(tu/deftest-kb the-diagonal-entails-but-supports-nothing-so-it-concludes-nothing
  (tu/with-terms [RegA RegB reflexive CxDiagonalSpace]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxDiagonalSpace 'CxWell) 'CxUniverse
                {:strength :monotonic})
      (v/assert kb (list 'arg reflexive 1 'thing) 'CxUniverse {:strength :monotonic})
      ;; hasRegionPart contains the identity and has no `reflexive` declaration, so
      ;; (hasRegionPart ?x ?x) is entailed of every region by the algebra alone — with no
      ;; stored fact behind it
      (v/assert-rule kb [(list 'hasRegionPart '?x '?x)] (list reflexive '?x)
                     CxDiagonalSpace {:direction :forward})
      (v/assert kb (list 'nonTangentialProperPart RegA RegB) CxDiagonalSpace
                {:strength :monotonic})
      (testing "the algebra's identity is not evidence: a conclusion drawn from it would
                rest on nothing retractable, so the empty support is dropped"
        (is (empty? (v/sentexes-matching kb (list reflexive RegA) '?ctx)))
        (is (= #{:eq} (v/possible-relations kb :rcc8 CxDiagonalSpace RegA RegA))
            "the diagonal is still entailed — it is only unusable as support")))))

(tu/deftest-kb the-diagonal-of-a-declared-reflexive-predicate-rests-on-the-declaration
  ;; `(reflexive partOfRegion)` ships in CxUniverse
  (tu/with-terms [RegA RegB selfPart CxDiagonalSpace]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxDiagonalSpace 'CxWell) 'CxUniverse
                {:strength :monotonic})
      (v/assert kb (list 'arg selfPart 1 'thing) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list 'partOfRegion '?x '?x)] (list selfPart '?x)
                     CxDiagonalSpace {:direction :forward})
      (v/assert kb (list 'nonTangentialProperPart RegA RegB) CxDiagonalSpace
                {:strength :monotonic})
      (let [decl (v/handle-of kb '(reflexive partOfRegion) 'CxUniverse)
            h    (v/handle-of kb (list selfPart RegA) CxDiagonalSpace)]
        (is (= #{(list selfPart RegA) (list selfPart RegB)}
               (set (map :sentence (v/sentexes-matching kb (list selfPart '?x) '?ctx)))))
        (is (contains? (set (keys (:nodes (v/why kb h)))) decl))))))

(tu/deftest-kb an-entailment-in-an-unsatisfiable-network-concludes-nothing
  (tu/with-terms [RegA RegB RegC contained CxClashChain]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxClashChain 'CxWell) 'CxUniverse
                {:strength :monotonic})
      (v/assert kb (list 'arg contained 1 'thing) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list contained '?x)
                     CxClashChain {:direction :forward})
      (nest! kb CxClashChain [RegA RegB RegC])
      (is (seq (v/sentexes-matching kb (list contained RegA) '?ctx)) "believed while consistent")
      (let [clash (v/assert kb (list 'spatiallyDisconnected RegA RegB) CxClashChain
                            {:strength :monotonic})]
        (testing "an impossible theory should not be mined for conclusions"
          (is (false? (:consistent? (v/qualitative-network kb :rcc8 CxClashChain))))
          (is (empty? (v/sentexes-matching kb (list contained RegA) '?ctx))
              "the conclusion goes, though every fact it listed as support is still believed
               — which is the whole reason this cannot ride on the antecedents alone"))
        (testing "and retracting the clash brings it back"
          (v/retract! kb clash)
          (is (true? (:consistent? (v/qualitative-network kb :rcc8 CxClashChain))))
          (is (seq (v/sentexes-matching kb (list contained RegA) '?ctx))
              "blocked, not destroyed — the same revival an excepted conclusion gets"))))))

(tu/deftest-kb a-firing-over-a-stored-calculus-fact-is-withdrawn-when-its-node-is-blocked
  ;; the antecedent matches the stored fact itself, not an entailment: the settle blocks
  ;; the firing, and no later join may place it again while the node stays blocked
  (tu/with-terms [RegA RegB contained CxStoredClash]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxStoredClash 'CxWell) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'arg contained 1 'thing) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list 'nonTangentialProperPart '?x '?y)] (list contained '?x)
                     CxStoredClash {:direction :forward})
      (v/assert kb (list 'nonTangentialProperPart RegA RegB) CxStoredClash
                {:strength :monotonic})
      (is (seq (v/sentexes-matching kb (list contained RegA) '?ctx)) "believed while consistent")
      (let [clash (v/assert kb (list 'spatiallyDisconnected RegA RegB) CxStoredClash
                            {:strength :monotonic})]
        (is (false? (:consistent? (v/qualitative-network kb :rcc8 CxStoredClash))))
        (is (empty? (v/sentexes-matching kb (list contained RegA) '?ctx))
            "withdrawn though the stored fact it matched is still believed")
        (v/retract! kb clash)
        (is (seq (v/sentexes-matching kb (list contained RegA) '?ctx))
            "and placed again once the network is satisfiable")))))

(tu/deftest-kb a-network-unsatisfiable-only-where-two-contexts-meet-withdraws-the-firing-there
  ;; Each side's network is satisfiable; only the context seeing both composes A ⊂ B ⊂ D
  ;; against A disconnected from D.  The settle asks the contexts where the facts meet, so
  ;; the firing placed there goes and the ones placed on either side stay.
  (tu/with-terms [RegA RegB RegD containedIn CxLeft CxRight CxMeet]
    (with-spatial kb
      (doseq [[sub sup] [[CxLeft 'CxWell] [CxRight 'CxWell] [CxMeet CxLeft] [CxMeet CxRight]]]
        (v/assert kb (list 'genlCx sub sup) 'CxUniverse {:strength :monotonic}))
      (doseq [n [1 2]]
        (v/assert kb (list 'arg containedIn n 'thing) 'CxUniverse {:strength :monotonic}))
      (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list containedIn '?x '?y)
                     'CxWell {:direction :forward})
      (v/assert kb (list 'nonTangentialProperPart RegA RegB) CxLeft {:strength :monotonic})
      (v/assert kb (list 'nonTangentialProperPart RegB RegD) CxRight {:strength :monotonic})
      (let [held? #(seq (v/sentexes-matching kb (list containedIn %1 %2) '?ctx))]
        (is (held? RegA RegD) "the pair only the meeting context composes fires there")
        (let [clash (v/assert kb (list 'spatiallyDisconnected RegA RegD) CxLeft
                              {:strength :monotonic})]
          (is (true? (:consistent? (v/qualitative-network kb :rcc8 CxLeft))))
          (is (false? (:consistent? (v/qualitative-network kb :rcc8 CxMeet))))
          (is (not (held? RegA RegD)) "withdrawn where the network is unsatisfiable")
          (is (held? RegA RegB) "the firing on the satisfiable side stays")
          (v/retract! kb clash)
          (is (held? RegA RegD) "and it comes back with the network"))))))

(defn- redecided
  "How many justifications `f` puts in front of `chain/justification-excepted?`."
  [f]
  (let [n (atom 0), orig chain/justification-excepted?]
    (with-redefs-fn {#'chain/justification-excepted? (fn [kb j] (swap! n inc) (orig kb j))}
      (fn [] (f) @n))))

(tu/deftest-kb an-arrival-over-a-satisfiable-network-re-decides-no-standing-firing
  ;; docs/exceptions.md, "Two withdrawals a firing carries": a satisfiable network
  ;; withdraws nothing, so the firings a rule over it stands on are not asked again
  (tu/with-terms [contained CxSteady]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxSteady 'CxWell) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'arg contained 1 'thing) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list contained '?x)
                     CxSteady {:direction :forward})
      (nest! kb CxSteady (into [] (repeatedly 6 #(tu/tmp-ind "Rs"))))
      (let [[a b] [(tu/tmp-ind "Rs") (tu/tmp-ind "Rs")]
            n     (redecided #(v/assert kb (list 'nonTangentialProperPart a b) CxSteady
                                        {:strength :monotonic}))]
        (is (zero? n) (str n " standing firings re-decided"))
        (is (seq (v/sentexes-matching kb (list contained a) '?ctx)) "the arrival fires")))))

;; ---- residency, counted -------------------------------------------------
;; The count side of docs/qcn.md's residency claim; `lein perf`'s `qcn-network-residency`
;; holds the cost side.

(defn- networks-built
  "How many networks `f` made the resident read build: a `with-redefs` on the private
  builder sees every miss and no hit."
  [f]
  (let [n (atom 0), orig @#'qkb/build-network]
    (with-redefs-fn {#'qkb/build-network (fn [& args] (swap! n inc) (apply orig args))}
      (fn [] (f) @n))))

(tu/deftest-kb network-reads-grow-with-the-calls-and-not-with-the-asserts
  (tu/with-terms [CxResidency]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxResidency 'CxWell) 'CxUniverse {:strength :monotonic})
      (let [chain! (fn [n]
                     (let [rs (into [] (repeatedly n #(tu/tmp-ind "Rr")))]
                       (nest! kb CxResidency rs)
                       rs))
            asked  (fn [rs] #(dotimes [_ 25]
                               (v/possible-relations kb :rcc8 CxResidency
                                                     (first rs) (peek rs))))
            small  (networks-built (asked (chain! 4)))
            ;; four times the asserts, over the same context and so the same cache key
            big    (networks-built (asked (chain! 16)))]
        (is (pos? small) "the fixture really does read a network")
        (is (< small 25) "twenty-five calls do not cost twenty-five reads")
        (is (= small big)
            (str "the read count is a function of what changed, not of what is stored — "
                 "4 regions cost " small " builds and 16 cost " big))))))

(tu/deftest-kb a-settle-over-calculus-facts-reads-no-network-and-still-files-an-unsatisfiable-one
  ;; docs/qcn.md, "The settle asks every write": past the first settle, a fact of the
  ;; calculus closes the recorded pass again from its own constraint
  (tu/with-terms [CxSettled]
    (with-spatial kb
      (v/assert kb (list 'genlCx CxSettled 'CxWell) 'CxUniverse {:strength :monotonic})
      (let [rs    (into [] (repeatedly 10 #(tu/tmp-ind "Rq")))
            filed #(filterv (fn [e] (and (= :qualitative-inconsistency (:violation e))
                                         (= CxSettled (:context e))))
                            (v/violations kb))
            clash (list 'spatiallyDisconnected (first rs) (peek rs))]
        (nest! kb CxSettled (subvec rs 0 2))
        (is (zero? (networks-built #(nest! kb CxSettled (subvec rs 1))))
            "eight writes, one fact each, read no network")
        (let [e (try (v/try-assert kb clash CxSettled {:strength :monotonic}) nil
                     (catch clojure.lang.ExceptionInfo e (ex-data e)))]
          (is (= :unsatisfiable-network (:violation e)) "try-assert refuses the closing fact")
          (is (empty? (filed))))
        (v/assert kb clash CxSettled {:strength :monotonic})
        (is (= 1 (count (filed))) "the write files the entry")
        (is (false? (:consistent? (v/qualitative-network kb :rcc8 CxSettled))))))))

(tu/deftest-kb an-assert-after-a-refused-try-assert-or-a-preview-of-it-files-the-unsatisfiable-entry
  (doseq [taken-back [:try-assert :preview]]
    (tu/with-terms [RegA RegB RegC CxRefused]
      (with-spatial kb
        (v/assert kb (list 'genlCx CxRefused 'CxWell) 'CxUniverse {:strength :monotonic})
        (nest! kb CxRefused [RegA RegB RegC])
        (let [clash  (list 'spatiallyDisconnected RegA RegC)
              filed  #(filterv (fn [e] (and (= :qualitative-inconsistency (:violation e))
                                            (= CxRefused (:context e))))
                               (v/violations kb))
              events (atom [])
              t      (v/watch kb #(swap! events conj %))]
          (try
            (case taken-back
              :try-assert (is (= :unsatisfiable-network
                                 (try (v/try-assert kb clash CxRefused {:strength :monotonic}) nil
                                      (catch clojure.lang.ExceptionInfo e (:violation (ex-data e))))))
              :preview    (is (some #(= :qualitative-inconsistency (:violation %))
                                    (:violations (v/preview kb {:add [[clash CxRefused {:strength :monotonic}]]})))
                              "the preview reports the entry"))
            (is (empty? (filed)) (str taken-back ": the write taken back files nothing"))
            (v/assert kb clash CxRefused {:strength :monotonic})
            (is (= 1 (count (filed))) (str taken-back ": the plain write files the entry"))
            (is (= (filed) (filterv #(= CxRefused (:context %)) (mapcat :unsatisfiable @events)))
                (str taken-back ": and a listener receives it"))
            (finally (v/unwatch kb t))))))))
