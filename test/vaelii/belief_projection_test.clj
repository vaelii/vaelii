;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.belief-projection-test
  "Modal belief projection — `(believes Agent P)` answered by proving `P` in `Agent`'s
  own context (`CxAgent<Agent>`) rather than in the asker's.

  The whole capability is one convention (`vaelii.impl.modal`) and one prover
  (`BeliefProjectionProver`) over the context lattice the engine already has, plus a
  `modal_predicate` grant that says which predicates project.  The contract these tests
  hold is that two agents may believe contradictory things without the KB being
  inconsistent — the property the lattice was built to give, and the one no
  Datalog / SPARQL / DL rival can field.  See docs/belief.md."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.modal :as modal]
            [vaelii.impl.naming :as naming]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private ask-ctx 'CxWell)

(defn- runs?
  "Does prover named `nm` (a record simple-name) actually run for `goal` asked in
  `ask-ctx`?"
  [kb goal nm]
  (boolean (some #(and (= nm (:prover %)) (:runs? %))
                 (v/query-plan kb goal ask-ctx))))

(defn- applies?
  "Is prover named `nm` even applicable to `goal` — does it appear in the plan at all?"
  [kb goal nm]
  (boolean (some #(= nm (:prover %)) (v/query-plan kb goal ask-ctx))))

;; ---- the convention: agent ↔ context, and legal names --------------------

(deftest the-agent-context-bijection-round-trips
  (testing "an agent maps to its context and back"
    (is (= 'CxAgentAlice (modal/context-of-agent 'Alice)))
    (is (= 'Alice (modal/agent-of-context 'CxAgentAlice)))
    (is (= 'Alice (-> 'Alice modal/context-of-agent modal/agent-of-context))))
  (testing "an agent context is recognized; an ordinary context is not"
    (is (modal/agent-context? 'CxAgentAlice))
    (is (not (modal/agent-context? 'CxUniverse)))
    (is (nil? (modal/agent-of-context 'CxUniverse))))
  (testing "a generated agent-context name passes naming's own context check (invariant)"
    (doseq [a '[Alice Bob Tweety Agent1 X]]
      (is (naming/context? (modal/context-of-agent a))
          (str "CxAgent" a " must be a legal context name")))))

(deftest projectability-is-ground-agent-plus-legal-name
  (testing "a ground individual agent is projectable"
    (is (modal/projectable-agent? 'Alice)))
  (testing "an unbound ?variable agent is not — its context name would carry a ?"
    (is (not (modal/projectable-agent? '?who)))
    (is (not (naming/context? (modal/context-of-agent '?who)))))
  (testing "a non-symbol or compound agent is not projectable"
    (is (not (modal/projectable-agent? 42)))
    (is (not (modal/projectable-agent? '(flies Tweety)))))
  (testing "the bare prefix is not itself an agent context"
    (is (not (modal/agent-context? 'CxAgent)))
    (is (nil? (modal/agent-of-context 'CxAgent)))))

;; ---- the headline: N agents, one belief each -----------------------------

(defn- believe!
  "Assert that `agent` believes `sentence` by placing `sentence` in the agent's context
  directly — the stage-1 query-only path: the caller asserts, the projector reads back."
  [kb agent sentence]
  (v/assert kb sentence (modal/context-of-agent agent)))

(tu/deftest-kb the-wmodal-shape-each-agent-projects-its-own-belief
  ;; three agents, each asserted one fact in its own context
  (believe! kb 'Alice '(flies Tweety))
  (believe! kb 'Bob   '(swims Nemo))
  (believe! kb 'Cara  '(runs Bolt))
  (testing "every agent believes its own fact"
    (is (v/ask? kb '(believes Alice (flies Tweety)) ask-ctx))
    (is (v/ask? kb '(believes Bob   (swims Nemo))   ask-ctx))
    (is (v/ask? kb '(believes Cara  (runs Bolt))    ask-ctx)))
  (testing "no agent believes another's fact — the contexts do not leak into each other"
    (is (not (v/ask? kb '(believes Alice (swims Nemo))   ask-ctx)))
    (is (not (v/ask? kb '(believes Bob   (flies Tweety)) ask-ctx)))
    (is (not (v/ask? kb '(believes Cara  (flies Tweety)) ask-ctx))))
  (testing "base sees none of them — a belief is not a claim of the KB"
    (is (not (v/ask? kb '(flies Tweety) ask-ctx)))
    (is (not (v/ask? kb '(swims Nemo)   ask-ctx)))))

(tu/deftest-kb a-variable-in-the-proposition-binds-through-the-projection
  (believe! kb 'Alice '(flies Tweety))
  (believe! kb 'Alice '(flies Robin))
  (testing "the inner query's bindings project straight back out to the asker"
    (is (= #{'Tweety 'Robin}
           (into #{} (map '?x) (v/ask kb '(believes Alice (flies ?x)) ask-ctx))))))

;; ---- the contract: contradictory agents coexist --------------------------

(tu/deftest-kb contradictory-agents-raise-no-contradiction
  (believe! kb 'Alice '(flies Tweety))
  (believe! kb 'Bob   '(not (flies Tweety)))
  (testing "each agent projects its own belief"
    (is (v/ask? kb '(believes Alice (flies Tweety))       ask-ctx))
    (is (v/ask? kb '(believes Bob   (not (flies Tweety))) ask-ctx)))
  (testing "and neither the positive nor the negative is a belief of the other"
    (is (not (v/ask? kb '(believes Alice (not (flies Tweety))) ask-ctx)))
    (is (not (v/ask? kb '(believes Bob   (flies Tweety))       ask-ctx))))
  (testing "base holds neither"
    (is (not (v/ask? kb '(flies Tweety)       ask-ctx)))
    (is (not (v/ask? kb '(not (flies Tweety)) ask-ctx))))
  (testing "and no contradiction is recorded — the headline property of the lattice.
            The two beliefs share no context, so no settle ever sees the clash: neither
            an irreducible conflict nor a represented dilemma is raised about them."
    (is (empty? (v/conflicts kb)))
    (is (empty? (v/contradictions kb)))))

;; ---- the ground check: an unbound agent is not the projector's ----------

(tu/deftest-kb an-unbound-agent-is-not-claimed-by-the-projector
  (believe! kb 'Alice '(flies Tweety))
  (testing "with a ground agent the projector runs"
    (is (runs? kb '(believes Alice (flies Tweety)) "BeliefProjectionProver")))
  (testing "with an unbound agent it is not even applicable — that is a different, "
    ;; "search every agent's context" query, deliberately excluded
    (is (not (applies? kb '(believes ?who (flies Tweety)) "BeliefProjectionProver")))))

;; ---- registration: the table is open, and closed by default --------------

(tu/deftest-kb a-second-modal-predicate-registered-at-runtime-projects-identically
  ;; before registration, `knows` is an ordinary predicate — not projected.  The starter's
  ;; `(binary_predicate knows)` has a copy in CxUniverse, which every context sees.
  (believe! kb 'Alice '(dreamsOf Alice Wonderland))
  (is (not (applies? kb '(knows Alice (dreamsOf Alice Wonderland))
                     "BeliefProjectionProver"))
      "an unregistered predicate is not the projector's")
  ;; grant it, and the same projection now answers it
  (v/register-modal-predicate kb 'knows)
  (is (runs? kb '(knows Alice (dreamsOf Alice Wonderland)) "BeliefProjectionProver")
      "a registered predicate projects like believes")
  (is (v/ask? kb '(knows Alice (dreamsOf Alice Wonderland)) ask-ctx)))

;; ---- independence vs. inheritance opt-in ---------------------------------

(tu/deftest-kb an-agent-sees-the-definitional-layer-and-opts-into-contingent-facts
  ;; a contingent fact sits in CxWell, which an agent context sees only through an edge
  (v/assert kb '(green Grass) 'CxWell)
  (testing "an agent with no genlCx edge reads CxUniverse"
    (is (v/ask? kb '(believes Alice (genl dog mammal)) ask-ctx)))
  (testing "and does not believe a fact stated in CxWell"
    (is (not (v/ask? kb '(believes Alice (green Grass)) ask-ctx))))
  (testing "an agent that opts in (genlCx to CxWell) does"
    (v/assert kb '(genlCx CxAgentBob CxWell) 'CxUniverse)
    (is (v/ask? kb '(believes Bob (green Grass)) ask-ctx))))

;; ---- believes stays an ordinary, assertible relation ---------------------

(tu/deftest-kb a-stored-believes-fact-is-answerable-and-not-double-counted
  ;; assert (believes Alice P) as a *fact* — no projection set up for it
  (v/assert kb '(believes Alice (barks Rex)) ask-ctx)
  (testing "the fact prover answers a stored believes with the projector registered"
    (is (v/ask? kb '(believes Alice (barks Rex)) ask-ctx))
    (is (runs? kb '(believes Alice (barks Rex)) "FactProver")))
  (testing "and it is not double-counted when the projection would also hold"
    ;; also make the projection hold: place the same P in Alice's context
    (believe! kb 'Alice '(barks Rex))
    (is (= 1 (count (v/ask kb '(believes Alice (barks Rex)) ask-ctx)))
        "the stored fact and the projected answer are one distinct solution")))

;; ---- no leakage, both directions (invariant 4) --------------------------

(tu/deftest-kb a-fact-only-in-the-askers-context-is-not-a-belief
  ;; the reverse of the headline's cross-agent check: the projector reads the *agent's*
  ;; context, so a fact that lives only where the question is asked is not believed.
  (v/assert kb '(flies Zephyr) ask-ctx)               ; in CxWell, never in an agent ctx
  (testing "base holds it"
    (is (v/ask? kb '(flies Zephyr) ask-ctx)))
  (testing "but no agent believes it — solve discards the asker's context on purpose"
    (is (not (v/ask? kb '(believes Alice (flies Zephyr)) ask-ctx)))
    (is (not (v/ask? kb '(believes Bob   (flies Zephyr)) ask-ctx)))))

;; ---- the projection composes with the whole registry, not just facts ----

(tu/deftest-kb a-projected-query-reaches-the-taxonomy-closure-not-only-stored-facts
  ;; everything an agent's beliefs need is in the agent's context, and the projection
  ;; runs the *whole* registry there — so a type derived through genl is believed even
  ;; though no `(birdOfPrey Kes)` fact was ever stored.
  (let [actx (modal/context-of-agent 'Alice)]
    (v/assert kb '(genl kestrel7 raptor7) actx)
    (v/assert kb '(kestrel7 Kes7) actx)
    (testing "the derived type membership projects"
      (is (v/ask? kb '(believes Alice (raptor7 Kes7)) ask-ctx)))
    (testing "and it is genuinely the agent's — base does not derive it"
      (is (not (v/ask? kb '(raptor7 Kes7) ask-ctx))))))

;; ---- registration is scoped to the granting context ----------------------

(tu/deftest-kb a-modal-grant-is-a-policy-of-the-context-that-holds-it
  (believe! kb 'Alice '(sings Lark))
  (v/assert kb '(binary_predicate deems) 'CxPsych)     ; a predicate CxPsych can see
  (v/register-modal-predicate kb 'deems 'CxPsych)     ; granted modal *only* in CxPsych
  (let [goal '(deems Alice (sings Lark))]
    (testing "asked from the granting context, the projector runs and answers"
      (is (some #(and (= "BeliefProjectionProver" (:prover %)) (:runs? %))
                (v/query-plan kb goal 'CxPsych)))
      (is (v/ask? kb goal 'CxPsych)))
    (testing "asked from a context that cannot see the grant, it is not claimed"
      (is (not (some #(= "BeliefProjectionProver" (:prover %))
                     (v/query-plan kb goal ask-ctx))))
      (is (not (v/ask? kb goal ask-ctx))))))

;; ---- belief follows retraction, and so does the grant -------------------

(tu/deftest-kb retracting-a-belief-or-its-grant-turns-the-answer-off
  (testing "retracting the belief fact ends the projection"
    (believe! kb 'Cara '(runs Bolt))
    (is (v/ask? kb '(believes Cara (runs Bolt)) ask-ctx))
    (v/retract! kb (v/handle-of kb '(runs Bolt) (modal/context-of-agent 'Cara)))
    (is (not (v/ask? kb '(believes Cara (runs Bolt)) ask-ctx))))
  (testing "retracting the modal_predicate grant ends projection for that predicate"
    (v/assert kb '(binary_predicate hopes) 'CxUniverse)
    (v/register-modal-predicate kb 'hopes)            ; granted in CxUniverse
    (believe! kb 'Cara '(wins Race))
    (is (runs? kb '(hopes Cara (wins Race)) "BeliefProjectionProver"))
    (v/retract! kb (v/handle-of kb '(modal_predicate hopes) 'CxUniverse))
    (is (not (applies? kb '(hopes Cara (wins Race)) "BeliefProjectionProver")))))

;; ---- nested belief: only where the marker is visible --------------------

(tu/deftest-kb nested-belief-projects-only-where-the-grant-is-visible
  (v/assert kb '(purrs Cat) (modal/context-of-agent 'Bob))
  (testing "the shipped believes grant is in CxUniverse, which Alice's context sees, so the
            nesting projects through"
    (is (v/ask? kb '(believes Alice (believes Bob (purrs Cat))) ask-ctx)))
  (tu/with-terms [thinks]
    (v/assert kb (list 'binary_predicate thinks) 'CxUniverse)
    (v/assert kb (list 'modal_predicate thinks) ask-ctx)
    (let [nested (list thinks 'Alice (list thinks 'Bob '(purrs Cat)))]
      (testing "a grant in CxWell is invisible from Alice's context, so the inner literal
                is read plainly — false, no recursion"
        (is (not (v/ask? kb nested ask-ctx))))
      (testing "once Alice's context sees the grant, the nesting projects through"
        (v/assert kb (list 'genlCx (modal/context-of-agent 'Alice) ask-ctx) 'CxUniverse)
        (is (v/ask? kb nested ask-ctx))))))

;; ---- the prover's declared cost, and graceful non-claims ----------------

(tu/deftest-kb the-projector-declares-compute-cost-and-augmenting-completeness
  (believe! kb 'Alice '(flies Tweety))
  (let [entry (first (filter #(= "BeliefProjectionProver" (:prover %))
                             (v/query-plan kb '(believes Alice (flies Tweety)) ask-ctx)))]
    (is (= :compute (:cost entry)) "a projection is a sub-query, never a lookup")
    (is (= 50 (:completeness entry)) "it augments the fact prover, never runs alone")))

(tu/deftest-kb the-projector-declines-shapes-that-are-not-a-belief-goal
  (testing "a non-sentence proposition is left to the fact prover"
    (is (not (applies? kb '(believes Alice PlainThing) "BeliefProjectionProver"))))
  (testing "an agent with no context yet answers false, not an error"
    (is (not (v/ask? kb '(believes Ghost (flies Tweety)) ask-ctx)))))

;; ---- the grant survives a rebuild (invariant: a restart changes no answer) ----

(tu/deftest-kb belief-projection-survives-recover
  ;; The `modal_predicate` grant is a taxonomy prop rebuilt from the stored
  ;; `(modal_predicate P)` fact — the same shape as genlArg's mark (arggenl_test) — so a
  ;; rebuild must reconstruct the grant, else a recovered KB would stop projecting a belief
  ;; the running one answered: a restart changing an answer.  Covers both the shipped
  ;; `believes` grant and a runtime-registered one.
  (believe! kb 'Alice '(flies Tweety))
  (v/register-modal-predicate kb 'knows)                  ; a runtime grant, stored in CxUniverse
  (believe! kb 'Alice '(dreamsOf Alice Wonderland))
  (testing "both the shipped and the runtime grant project before the rebuild"
    (is (runs? kb '(believes Alice (flies Tweety)) "BeliefProjectionProver"))
    (is (v/ask? kb '(believes Alice (flies Tweety)) ask-ctx))
    (is (v/ask? kb '(knows Alice (dreamsOf Alice Wonderland)) ask-ctx)))
  (v/recover kb)
  (testing "the :modal prop cache rebuilds from the stored grants, so the projector still runs"
    (is (runs? kb '(believes Alice (flies Tweety)) "BeliefProjectionProver"))
    (is (runs? kb '(knows Alice (dreamsOf Alice Wonderland)) "BeliefProjectionProver")))
  (testing "and the same beliefs still project after recover"
    (is (v/ask? kb '(believes Alice (flies Tweety)) ask-ctx))
    (is (v/ask? kb '(knows Alice (dreamsOf Alice Wonderland)) ask-ctx))))
