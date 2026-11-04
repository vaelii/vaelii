;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.transitive-chain-test
  "Forward chaining across a transitive predicate's closure.

  A rule antecedent on a `(transitive P)` predicate matches stored edges, and a pair two
  hops apart is stored nowhere — so on its own the rule fires across one hop and a
  narrative has to write down the pairs it wants read.  The join reads the closure
  instead, and `TransitivePredicateProver` reports the edges each answer crossed, so the
  firing rests on that chain and the ordinary relabel takes the conclusion away when any
  hop of it goes.

  Three things, then, and none of them is really about deriving: that the conclusion
  arrives across two hops, that `why` names the edges behind it, and that the answer does
  not depend on which hop arrived last."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private W 'CxWell)

(defn- causal-rule!
  "*Whatever a spark leads to is traceable to it* — a rule whose second antecedent is on a
  declared-transitive predicate, with the first binding one end of the walk."
  [kb {:keys [causes spark traceable]}]
  (v/assert kb (list 'transitive causes) W {:strength :monotonic})
  (v/assert kb (list 'implies (list 'and (list spark '?a) (list causes '?a '?c))
                     (list traceable '?a '?c))
            W {:direction :forward}))

(tu/deftest-kb a-forward-rule-fires-across-two-stored-hops
  (tu/with-terms [causes spark traceable Spark Fire Alarm]
    (let [world {:causes causes :spark spark :traceable traceable}]
      (causal-rule! kb world)
      (v/assert kb (list spark Spark) W)
      (v/assert kb (list causes Spark Fire) W)
      (let [second-hop (v/assert kb (list causes Fire Alarm) W)]
        (testing "one hop is the ordinary match"
          (is (v/ask? kb (list traceable Spark Fire) W)))
        (testing "and two hops is the walk, which no stored fact records"
          (is (v/ask? kb (list traceable Spark Alarm) W))
          (is (empty? (v/sentexes-matching kb (list causes Spark Alarm) '?ctx))
              "nothing stored the far pair — it is the closure that reached it"))
        (testing "the firing rests on the edges it crossed"
          (let [h     (v/handle-of kb (list traceable Spark Alarm) W)
                named (set (keys (:nodes (v/why kb h))))]
            (is (contains? named second-hop)
                "the second hop is named, so retracting it can reach the conclusion")))
        (testing "and the middle hop going takes the far conclusion and not the near one"
          (v/retract! kb second-hop)
          (is (not (v/ask? kb (list traceable Spark Alarm) W)))
          (is (nil? (v/handle-of kb (list traceable Spark Alarm) W))
              "withdrawn, not merely disbelieved")
          (is (v/ask? kb (list traceable Spark Fire) W)
              "the near pair rests on an edge that is still there"))))))

(tu/deftest-kb the-chain-reads-the-same-whichever-hop-arrived-last
  ;; An edge is not the tuple the rule fires at — it makes pairs *through* itself, and the
  ;; trigger index offers only the tuple it is stated at.  So an arriving edge re-joins the
  ;; rules carrying such an antecedent, and this is what says the re-join happens in both
  ;; directions.
  (doseq [[label near-first?] [["near hop first" true] ["far hop first" false]]]
    (testing label
      (tu/with-terms [causes spark traceable Spark Fire Alarm]
        (let [world {:causes causes :spark spark :traceable traceable}
              near! #(v/assert kb (list causes Spark Fire) W)
              far!  #(v/assert kb (list causes Fire Alarm) W)]
          (causal-rule! kb world)
          (v/assert kb (list spark Spark) W)
          (if near-first? (do (near!) (far!)) (do (far!) (near!)))
          (is (v/ask? kb (list traceable Spark Alarm) W)))))))

(tu/deftest-kb the-rule-arriving-last-reads-the-same-chain
  (tu/with-terms [causes spark traceable Spark Fire Alarm]
    (v/assert kb (list 'transitive causes) W {:strength :monotonic})
    (v/assert kb (list spark Spark) W)
    (v/assert kb (list causes Spark Fire) W)
    (v/assert kb (list causes Fire Alarm) W)
    (v/assert kb (list 'implies (list 'and (list spark '?a) (list causes '?a '?c))
                       (list traceable '?a '?c))
              W {:direction :forward})
    (is (v/ask? kb (list traceable Spark Alarm) W)
        "a rule stored after the chain joins over the closure at its own firing")))

(tu/deftest-kb the-declaration-arriving-last-turns-the-walk-on
  ;; `(transitive causes)` is what makes the antecedent a walk at all, and the edges it
  ;; walks have already arrived by the time it lands — so nothing about `causes` would ever
  ;; bring the rule round again.  The declaration re-joins them, as a `(symmetric P)` does.
  (tu/with-terms [causes spark traceable Spark Fire Alarm]
    (v/assert kb (list 'implies (list 'and (list spark '?a) (list causes '?a '?c))
                       (list traceable '?a '?c))
              W {:direction :forward})
    (v/assert kb (list spark Spark) W)
    (v/assert kb (list causes Spark Fire) W)
    (v/assert kb (list causes Fire Alarm) W)
    (is (not (v/ask? kb (list traceable Spark Alarm) W))
        "undeclared, the antecedent matches stored edges and nothing else")
    (v/assert kb (list 'transitive causes) W {:strength :monotonic})
    (is (v/ask? kb (list traceable Spark Alarm) W)
        "and the declaration brings the rule round over the chain already there")))

(tu/deftest-kb a-walk-is-placed-where-its-declaration-is-seen
  ;; The hops in one context and the declaration in a sibling.  `transitive` is lifted to
  ;; CxUniverse, which the hops' context sees, so the forward rule fires there over the
  ;; two hops.  The support names the declaration, which is what places the firing and
  ;; what lets retracting it withdraw the firing.
  (tu/with-terms [causes traced Spark Fire Alarm CxHops CxDecl]
    (let [decl (v/assert kb (list 'transitive causes) CxDecl {:strength :monotonic})]
      (v/assert kb (list causes Spark Fire) CxHops)
      (v/assert kb (list causes Fire Alarm) CxHops)
      (v/assert kb (list 'implies (list causes Spark '?c) (list traced '?c)) CxHops
                {:direction :forward})
      (testing "the far pair is derived where the hops see the declaration"
        (is (seq (v/sentexes-matching kb (list traced Alarm) CxHops)))
        (is (seq (v/sentexes-matching kb (list traced Fire) CxHops))
            "the one stored hop needs no declaration"))
      (testing "resting on the declaration it was walked under"
        (let [h     (v/handle-of kb (list traced Alarm) CxHops)
              named (set (keys (:nodes (v/why kb h))))]
          (is (contains? named decl))))
      (testing "and withdrawn with it"
        (v/retract! kb decl)
        (is (empty? (v/sentexes-matching kb (list traced Alarm) '?ctx)))))))

(tu/deftest-kb a-rule-that-concludes-what-it-would-walk-takes-the-matcher-alone
  ;; The written-out closure and the walk must not both run: a rule storing `(P x z)` from
  ;; `(P x y)` and `(P y z)` moves its own graph inside the fixpoint, so which chain was
  ;; shortest would depend on how far it had got.  It reaches every pair the walk would,
  ;; and each conclusion rests on the two hops it joined rather than on a chain.
  (tu/with-terms [causes Spark Fire Alarm]
    (v/assert kb (list 'transitive causes) W {:strength :monotonic})
    (v/assert kb (list 'implies (list 'and (list causes '?a '?b) (list causes '?b '?c))
                       (list causes '?a '?c))
              W {:direction :forward})
    (v/assert kb (list causes Spark Fire) W)
    (v/assert kb (list causes Fire Alarm) W)
    (testing "the pair two hops apart is derived, and stored as an ordinary fact"
      (is (seq (v/sentexes-matching kb (list causes Spark Alarm) W))))
    (testing "resting on the two hops the rule joined"
      (let [h     (v/handle-of kb (list causes Spark Alarm) W)
            named (set (keys (:nodes (v/why kb h))))]
        (is (contains? named (v/handle-of kb (list causes Fire Alarm) W)))))))

(tu/deftest-kb a-rule-concluding-a-more-general-predicate-still-walks-the-closure
  ;; The mirror of the test above, and the line between them.  The closure-join is
  ;; suppressed only for a rule concluding `pred` itself or a *sub*-predicate of it —
  ;; those conclusions are `pred`-edges by subsumption and the walk would find them.  A
  ;; rule concluding a *super*-predicate does not feed `pred`'s graph, so the walk and the
  ;; rule cannot disagree, and the walk must run or a two-hop pair is silently lost.
  ;; `(genl before torder)` with a rule concluding `torder` from a `before` walk is the
  ;; shape; forward chaining must reach the far pair, agree with backward `ask`, and hold
  ;; whichever hop arrived last.
  (tu/with-terms [before torder begins A B C D]
    (v/assert kb (list 'transitive before) W {:strength :monotonic})
    (v/assert kb (list 'genl before torder) W {:strength :monotonic})
    (v/assert kb (list 'implies (list 'and (list begins '?x) (list before '?x '?y))
                       (list torder '?x '?y))
              W {:direction :forward})
    (v/assert kb (list begins A) W)
    (v/assert kb (list before A B) W)
    (v/assert kb (list before B C) W)
    (v/assert kb (list before C D) W)
    (testing "the rule fires across the walked closure, not only the one stored hop"
      (is (seq (v/sentexes-matching kb (list torder A D) W))
          "the three-hop pair is derived through the before-walk")
      (is (seq (v/sentexes-matching kb (list torder A C) W))))
    (testing "and agrees with backward chaining, which reaches the pair through the prover"
      (is (v/ask? kb (list torder A D) W))))
  (testing "and the far hop arriving last still brings the pair round"
    (tu/with-terms [before2 torder2 begins2 P Q R]
      (v/assert kb (list 'transitive before2) W {:strength :monotonic})
      (v/assert kb (list 'genl before2 torder2) W {:strength :monotonic})
      (v/assert kb (list 'implies (list 'and (list begins2 '?x) (list before2 '?x '?y))
                         (list torder2 '?x '?y))
                W {:direction :forward})
      (v/assert kb (list begins2 P) W)
      (v/assert kb (list before2 Q R) W)
      (v/assert kb (list before2 P Q) W)
      (is (seq (v/sentexes-matching kb (list torder2 P R) W))
          "the pair joins over the closure however the hops arrived"))))

(tu/deftest-kb a-defeated-hop-is-not-a-hop
  ;; The walk reads *believed* edges, so a stronger negation breaks the chain exactly as a
  ;; retraction does — and reviving the edge brings the conclusion back.
  (tu/with-terms [causes spark traceable Spark Fire Alarm]
    (causal-rule! kb {:causes causes :spark spark :traceable traceable})
    (v/assert kb (list spark Spark) W)
    (let [near (v/assert kb (list causes Spark Fire) W {:strength :default})]
      (v/assert kb (list causes Fire Alarm) W)
      (is (v/ask? kb (list traceable Spark Alarm) W))
      (let [d (v/assert kb (list 'not (list causes Spark Fire)) W {:strength :monotonic})]
        (is (not (v/in? kb near)) "the stronger negation defeats the first hop")
        (is (not (v/ask? kb (list traceable Spark Alarm) W))
            "so the chain is broken and the far conclusion goes")
        (v/retract! kb d)
        (is (v/in? kb near) "the edge revives...")
        (is (v/ask? kb (list traceable Spark Alarm) W) "...and so does the conclusion")))))

(tu/deftest-kb a-join-binding-both-ends-walks-a-diamond-and-a-cycle
  ;; the first rule binds both ends of the walk before it, so the join asks a ground pair
  ;; across a diamond (two routes to one node); the second asks a node back to itself
  (tu/with-terms [causes spark target alarmOf loops A B C D]
    (v/assert kb (list 'transitive causes) W {:strength :monotonic})
    (v/assert kb (list 'implies (list 'and (list spark '?a) (list target '?d) (list causes '?a '?d))
                       (list alarmOf '?a '?d))
              W {:direction :forward})
    (v/assert kb (list 'implies (list 'and (list spark '?a) (list causes '?a '?a)) (list loops '?a))
              W {:direction :forward})
    (v/assert kb (list spark A) W)
    (v/assert kb (list target D) W)
    (doseq [[x y] [[A B] [A C] [B D] [C D]]] (v/assert kb (list causes x y) W))
    (is (= [(list alarmOf A D)] (map :sentence (v/sentexes-matching kb (list alarmOf '?a '?d) W))))
    (is (empty? (v/sentexes-matching kb (list loops '?a) W)) "no route leads back yet")
    (let [back (v/assert kb (list causes D A) W)]
      (is (= [(list loops A)] (map :sentence (v/sentexes-matching kb (list loops '?a) W))))
      (v/retract! kb back)
      (is (empty? (v/sentexes-matching kb (list loops '?a) W))
          "the loop rests on the edge that closed it"))))

(tu/deftest-kb a-self-pair-antecedent-walks-every-node-back-to-itself
  ;; `(causes ?x ?x)` binds neither end, so the join enumerates the nodes on a cycle
  (tu/with-terms [causes loops A B C]
    (v/assert kb (list 'transitive causes) W {:strength :monotonic})
    (v/assert kb (list 'implies (list causes '?x '?x) (list loops '?x)) W {:direction :forward})
    (doseq [[x y] [[A B] [B A] [C A]]] (v/assert kb (list causes x y) W))
    (is (= #{(list loops A) (list loops B)}
           (set (map :sentence (v/sentexes-matching kb (list loops '?x) W))))
        "C reaches the cycle and is not on it")))
