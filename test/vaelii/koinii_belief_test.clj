;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-belief-test
  "Koinii belief projection + own-statement disregard.  `(believes agent P)` is proved in
  the agent's OWN context, so agents disagree without the KB contradicting itself and
  asking what one holds never pulls in another's.  `disregard` lets an agent reversibly
  withdraw its OWN statement (an `except`) — and only its own: hiding another agent's
  claim with an index-layer mask would break argumentation, so cross-agent disagreement
  is `dispute` / argue, not this."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.koinii.belief :as bel]
            [vaelii.koinii.identity :as id]
            [vaelii.test-util :as tu])
  (:import (clojure.lang ExceptionInfo)))

(defn- belief-kb
  "A fresh CxCore KB, restored by `tu/load-core!` — CxCore carries the `believes`
  modal_predicate grant, and its load wires `(genlCx CxUniverse CxCore)` so a modal goal
  asked from CxUniverse is recognized."
  []
  (tu/load-core! (tu/fresh)))

(use-fixtures :each (tu/neutral-fresh belief-kb))

(defn- holds!
  "`agent` asserts `claim` into its own koinii context, stamped as its creator.  Returns
  the claim's handle."
  [kb agent claim]
  (v/assert kb claim (id/context-for agent) {:creator agent}))

(defn- believes!
  "`agent` holds `belief` directly in its belief context — the belief.md
  stage-1 shape, where the caller asserts an agent's beliefs and the projector reads them."
  [kb agent belief]
  (v/assert kb belief (bel/belief-context agent) {:creator agent}))

;; ---- projection: read what an agent holds, from its own context ----------

(tu/deftest-kb an-agent-believes-its-own-claims-and-no-others
  (let [P '(usesDatabase ProdCluster PostgreSQL14)]
    (testing "before anything, the agent is independent — it believes nothing"
      (is (not (bel/would-believe? kb 'AgentAtlas P))))
    (bel/believe-own kb 'AgentAtlas)
    (holds! kb 'AgentAtlas P)
    (testing "with its koinii context linked, the agent believes what it asserted"
      (is (bel/would-believe? kb 'AgentAtlas P)))
    (testing "another agent does not — beliefs are proved in the holder's own context, never merged"
      (is (not (bel/would-believe? kb 'AgentBoreas P))))
    (testing "and base believes nothing — a belief is not a claim of the KB"
      (is (not (v/ask? kb P 'CxUniverse))))))

(tu/deftest-kb contradictory-agents-raise-no-contradiction
  (bel/believe-own kb 'AgentAtlas)
  (bel/believe-own kb 'AgentBoreas)
  (holds! kb 'AgentAtlas '(reliable ProdCluster))
  (holds! kb 'AgentBoreas '(not (reliable ProdCluster)))
  (testing "each agent projects its own belief, neither holds the other's"
    (is (bel/would-believe? kb 'AgentAtlas '(reliable ProdCluster)))
    (is (bel/would-believe? kb 'AgentBoreas '(not (reliable ProdCluster))))
    (is (not (bel/would-believe? kb 'AgentAtlas '(not (reliable ProdCluster)))))
    (is (not (bel/would-believe? kb 'AgentBoreas '(reliable ProdCluster)))))
  (testing "no contradiction is raised — the beliefs share no context (the lattice property)"
    (is (empty? (v/conflicts kb)))
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb project-binds-variables-from-the-agents-context
  (bel/believe-own kb 'AgentAtlas)
  (holds! kb 'AgentAtlas '(usesDatabase ProdCluster PostgreSQL14))
  (holds! kb 'AgentAtlas '(usesDatabase ProdCluster RedisCache))
  (is (= #{'PostgreSQL14 'RedisCache}
         (into #{} (map '?db) (bel/project kb 'AgentAtlas '(usesDatabase ProdCluster ?db))))
      "the DBs Atlas holds ProdCluster uses, recovered as bindings"))

;; ---- disregard: an agent reversibly withdraws its OWN statement -----------

(tu/deftest-kb an-agent-reversibly-withdraws-its-own-statement
  (let [P '(usesDatabase ProdCluster PostgreSQL14)]
    (bel/believe-own kb 'AgentAtlas)
    (v/assert kb (list 'genlCx 'CxDeploy (id/context-for 'AgentAtlas)) 'CxUniverse
              {:strength :monotonic})                        ; a channel that reads Atlas
    (let [h (holds! kb 'AgentAtlas P)]
      (testing "the claim is visible to the channel and to Atlas's own beliefs"
        (is (v/ask? kb P 'CxDeploy))
        (is (bel/would-believe? kb 'AgentAtlas P)))
      (let [eh (bel/disregard kb 'AgentAtlas h)]
        (testing "disregarded — withdrawn from view, but NOT deleted"
          (is (not (v/ask? kb P 'CxDeploy)) "gone from the channel view")
          (is (not (bel/would-believe? kb 'AgentAtlas P)) "and from Atlas's own beliefs")
          (is (some? (v/sentex kb h)) "the statement still exists — reversible, not retracted"))
        (bel/restore! kb eh)
        (testing "restored — except is belief-following"
          (is (v/ask? kb P 'CxDeploy))
          (is (bel/would-believe? kb 'AgentAtlas P)))))))

(tu/deftest-kb an-agent-cannot-disregard-another-agents-statement
  (let [P '(usesDatabase ProdCluster PostgreSQL14)]
    (bel/believe-own kb 'AgentAtlas)
    (let [h (holds! kb 'AgentAtlas P)]              ; Atlas's statement, creator AgentAtlas
      (testing "Boreas may not except a claim he does not own — that is argue's job, not except's"
        (let [d (try (bel/disregard kb 'AgentBoreas h)
                     nil
                     (catch ExceptionInfo e (ex-data e)))]
          (is (= :koinii/not-own-statement (:type d)))
          (is (= 'AgentBoreas (:agent d)))
          (is (= 'AgentAtlas (:creator d))
              "and it names whose statement it is, so the caller can go and dispute it")))
      (testing "and nothing was hidden — Atlas's claim stands"
        (is (empty? (bel/disregards kb 'AgentBoreas)))
        (is (bel/would-believe? kb 'AgentAtlas P))))))

(tu/deftest-kb disregards-are-queryable-and-do-not-cascade
  (let [P '(usesDatabase ProdCluster PostgreSQL14)]
    (bel/believe-own kb 'AgentAtlas)
    (let [h (holds! kb 'AgentAtlas P)]
      (bel/disregard kb 'AgentAtlas h)
      (testing "'what has Atlas withdrawn' is a plain read, and it is per-agent"
        (is (= 1 (count (bel/disregards kb 'AgentAtlas))))
        (is (empty? (bel/disregards kb 'AgentBoreas))))
      (testing "the disregard is UNMARKED — except never carries target_following_predicate"
        (is (not (v/has-prop? kb :target-following 'except))))
      (testing "so a later hard retract of the statement leaves the except a harmless orphan"
        (v/retract! kb h)
        (is (not (v/ask? kb P (id/context-for 'AgentAtlas))) "the statement is now really gone")
        (is (seq (bel/disregards kb 'AgentAtlas)) "the except orphans harmlessly, not swept")))))

;; ---- convene: bring isolated beliefs into one arena to argue --------------

(tu/deftest-kb convene-surfaces-otherwise-isolated-belief-disagreements
  (believes! kb 'AgentAtlas  '(reliable ProdCluster))
  (believes! kb 'AgentBoreas '(not (reliable ProdCluster)))
  (testing "isolated belief contexts share no ancestor — the clash is silent"
    (is (empty? (v/contradictions kb))))
  (bel/convene kb 'CxArbiter '[AgentAtlas AgentBoreas])
  (testing "convening a context that sees both raises the contradiction"
    (let [ds (bel/disagreements kb 'CxArbiter)]
      (is (= 1 (count ds)))
      (is (= #{'AgentAtlas 'AgentBoreas} (:between (first ds))))
      (is (= 2 (count (:sides (first ds)))) "both sides, each with its agent")
      (is (= #{'AgentAtlas 'AgentBoreas} (into #{} (map :agent) (:sides (first ds)))))
      (is (every? :handle (:sides (first ds))) "with a handle each, for 08/11 to act on"))))

(tu/deftest-kb convene-includes-only-the-agents-it-gathered
  (believes! kb 'AgentAtlas  '(reliable ProdCluster))
  (believes! kb 'AgentBoreas '(not (reliable ProdCluster)))
  (believes! kb 'AgentCiel   '(fast ProdCluster))            ; contradicts no one
  (bel/convene kb 'CxArbiter '[AgentAtlas AgentBoreas])     ; Ciel is not convened
  (is (= #{'AgentAtlas 'AgentBoreas} (bel/convened-agents kb 'CxArbiter)))
  (let [ds (bel/disagreements kb 'CxArbiter)]
    (is (= 1 (count ds)))
    (is (not (contains? (:between (first ds)) 'AgentCiel)))))

(tu/deftest-kb convene-works-over-koinii-claims-via-believe-own
  ;; the beliefs live in the agents' koinii WRITE contexts, seen through the belief
  ;; context by believe-own — disagreements maps the write-context side back to the agent
  (bel/believe-own kb 'AgentAtlas)
  (bel/believe-own kb 'AgentBoreas)
  (holds! kb 'AgentAtlas  '(reliable ProdCluster))
  (holds! kb 'AgentBoreas '(not (reliable ProdCluster)))
  (is (empty? (v/contradictions kb)) "no channel yet — nothing sees both")
  (bel/convene kb 'CxArbiter '[AgentAtlas AgentBoreas])
  (let [ds (bel/disagreements kb 'CxArbiter)]
    (is (= 1 (count ds)))
    (is (= #{'AgentAtlas 'AgentBoreas} (:between (first ds))))))

(tu/deftest-kb dissolving-the-arbiter-dissolves-the-contradiction
  (believes! kb 'AgentAtlas  '(reliable ProdCluster))
  (believes! kb 'AgentBoreas '(not (reliable ProdCluster)))
  (bel/convene kb 'CxArbiter '[AgentAtlas AgentBoreas])
  (is (seq (bel/disagreements kb 'CxArbiter)) "convened: the clash is visible")
  (let [gh (v/handle-of kb (list 'genlCx 'CxArbiter (bel/belief-context 'AgentAtlas)) 'CxUniverse)]
    (v/retract! kb gh))                                       ; arbiter no longer sees Atlas
  (testing "with the arbiter no longer seeing both sides, the contradiction dissolves"
    (is (empty? (v/contradictions kb)))
    (is (empty? (bel/disagreements kb 'CxArbiter)))))
