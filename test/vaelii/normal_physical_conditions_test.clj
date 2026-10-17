;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.normal-physical-conditions-test
  "CxNormalPhysicalConditions: the states of matter of stuff at ordinary room temperature
  and pressure, shipped as an opt-in theory below CxUniverse.  CxWell does not see the
  theory, so the everyday contexts below CxWell assume no temperature, and a user's own
  context opts in by placing itself under CxNormalPhysicalConditions.

  Stone, wood and glass are solid there through `genl` edges.  A metal is solid there by
  default, through a `set/defaultRule` whose `exceptWhen` names mercury, so a metal the KB
  says nothing more about comes out solid and a portion of mercury comes out liquid and
  not solid.  None of these states holds in a context that does not see the theory: a
  stone is solid at room temperature, and the upper ontology says nothing about the
  temperature."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private NPC 'CxNormalPhysicalConditions)

;; Each reader answers a boolean, so a failing `is` prints the question and not the KB.
(defn- holds-isa  [x t ctx]       (boolean (v/isa? tu/*kb* x t ctx)))
(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-sees [k y]           (boolean (v/sees? tu/*kb* k y)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))

(defn- in-clash?
  "Is the sentex `sentence` stored in `context` a member of a standing nogood?"
  [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (boolean (and h (some #(contains? (:nogood %) h)
                          (concat (v/contradictions kb) (v/conflicts kb)))))))

(tu/deftest-kb the-theory-is-opt-in-below-cxuniverse
  (testing "the theory sees the upper ontology through CxUniverse"
    (is (holds-sees NPC 'CxUniverse)))
  (testing "neither CxWell nor the upper ontology sees the theory"
    (is (not (holds-sees 'CxWell NPC)))
    (is (not (holds-sees 'CxUniverse NPC)))))

(tu/deftest-kb cxwell-concludes-no-state-of-matter
  ;; CxWell is the everyday context with no temperature assumed: a stone and a metal stated
  ;; there are not solid there.
  (tu/with-terms [Boulder Ingot]
    (v/assert kb (list 'stone Boulder) 'CxWell)
    (v/assert kb (list 'metal Ingot) 'CxWell)
    (is (not (holds-isa Boulder 'solid 'CxWell)))
    (is (not (holds-ask (list 'solid Ingot) 'CxWell)))
    (is (not (holds-isa Ingot 'solid 'CxWell)))))

(tu/deftest-kb mercury-is-a-first-order-kind-of-metal
  (is (holds-genl 'mercury 'metal 'CxUniverse))
  (is (holds-ask '(type mercury) 'CxUniverse))
  (is (seq (v/sentexes-matching kb '(comment mercury ?c) 'CxUniverse))))

(tu/deftest-kb stone-wood-and-glass-are-solid-under-normal-conditions
  (tu/with-terms [CxStuff CxRoom CxElsewhere Pebble Plank Pane]
    (v/assert kb (list 'genlCx CxStuff 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom CxStuff) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom NPC) 'CxUniverse)
    (v/assert kb (list 'genlCx CxElsewhere CxStuff) 'CxUniverse)
    (v/assert kb (list 'genlCx CxElsewhere 'CxWell) 'CxUniverse)
    (v/assert kb (list 'stone Pebble) CxStuff)
    (v/assert kb (list 'wood Plank) CxStuff)
    (v/assert kb (list 'glass_stuff Pane) CxStuff)
    (testing "a user context placed under the theory reads each one solid"
      (doseq [x [Pebble Plank Pane]]
        (is (holds-isa x 'solid CxRoom) (str x " is solid in a room"))
        (is (holds-ask (list 'solid x) CxRoom))))
    (testing "a context that does not see the theory concludes no state"
      (doseq [ctx [CxStuff CxElsewhere 'CxWell 'CxUniverse]
              x   [Pebble Plank Pane]]
        (is (not (holds-isa x 'solid ctx)) (str x " is not concluded solid in " ctx))))
    (testing "a phase is a state, not a kind: each is a default rule, not a genl edge"
      (doseq [t '[stone wood glass_stuff]]
        (is (not (holds-genl t 'solid NPC)))
        (is (holds-ask (list 'declined_rule_macro (list 'genl t 'solid)) NPC)))
      (doseq [x [Pebble Plank Pane]]
        (is (= :default (v/defeat-class kb (v/handle-of kb (list 'solid x) CxRoom))))))))

(tu/deftest-kb a-metal-is-solid-by-default-and-mercury-is-the-exception
  (tu/with-terms [CxStuff CxRoom CxElsewhere Nail Droplet]
    (v/assert kb (list 'genlCx CxStuff 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom CxStuff) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRoom NPC) 'CxUniverse)
    (v/assert kb (list 'genlCx CxElsewhere CxStuff) 'CxUniverse)
    (v/assert kb (list 'genlCx CxElsewhere 'CxWell) 'CxUniverse)
    (v/assert kb (list 'metal Nail) CxStuff)
    (v/assert kb (list 'mercury Droplet) CxStuff)
    (testing "a metal the KB says nothing more about is solid in a user context under the theory"
      (is (holds-ask (list 'solid Nail) CxRoom))
      (is (holds-isa Nail 'solid CxRoom)))
    (testing "the conclusion is a default, which a later fact can block"
      (let [h (v/handle-of kb (list 'solid Nail) CxRoom)]
        (is h "the firing is placed in the context below the rule and the fact")
        (is (= :default (v/defeat-class kb h)))))
    (testing "mercury is liquid and is not concluded solid"
      (is (holds-isa Droplet 'liquid CxRoom))
      (is (not (holds-genl 'mercury 'liquid NPC)) "liquid by a default rule, not a genl edge")
      (is (holds-ask '(declined_rule_macro (genl mercury liquid)) NPC))
      (is (holds-isa Droplet 'metal CxRoom))
      (is (not (holds-ask (list 'solid Droplet) CxRoom)))
      (is (not (holds-isa Droplet 'solid CxRoom)))
      (is (= :excepted (:reason (v/why-not kb (list 'solid Droplet) CxRoom)))
          "the rule applied and its exception held"))
    (testing "no clash is reported"
      (is (not (in-clash? kb (list 'mercury Droplet) CxStuff)))
      (is (not (in-clash? kb (list 'metal Nail) CxStuff)))
      (is (empty? (filter #(some #{Droplet Nail} (flatten (map :sentence (:sides %))))
                          (concat (v/contradictions kb) (v/conflicts kb))))))
    (testing "a context that does not see the theory concludes no state"
      (doseq [ctx [CxStuff CxElsewhere 'CxWell 'CxUniverse]]
        (is (not (holds-ask (list 'solid Nail) ctx)) (str "Nail solid in " ctx))
        (is (not (holds-isa Droplet 'liquid ctx)) (str "Droplet liquid in " ctx))))))
