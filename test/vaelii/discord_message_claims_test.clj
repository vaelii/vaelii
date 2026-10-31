;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.discord-message-claims-test
  "The Discord-message vocabulary of CxTra.  `(DiscordMessageFn ?snowflake)` names a
  `discord_message` by its snowflake id as a string, and `(discordMessageClaims ?message
  (sentexHandle H))` records that the message asserts what sentex H states.  The receipt
  is answered by either argument, follows its sentex out when the sentex is retracted,
  and a snowflake given as a number is refused."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(def ^:private message '(DiscordMessageFn "175928847299117063"))

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))
(defn- following? [p]             (boolean (v/has-prop? tu/*kb* :target-following p)))

(defn- problem-types
  "The `:type` of each problem `check` reports for `sentence` in `ctx`, or of the argument
  conviction `assert` holds it inert under."
  [sentence ctx]
  (tu/without-entailing
   (or (not-empty (mapv :type (v/check tu/*kb* sentence ctx)))
       (into [] (keep :type) [(tu/write-conviction tu/*kb* sentence ctx)]))))

(defn- desk!
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse)
  (v/assert kb (list 'genlCx ctx CPT) 'CxUniverse))

(tu/deftest-kb each-term-is-stated-in-the-theory-with-one-comment
  (doseq [t '[discord_message DiscordMessageFn discordMessageOf discordMessageClaims]]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment t '?c) CPT)))
        (str t " carries one comment in the theory")))
  (is (holds-genl 'discord_message 'digital_artifact CPT))
  (is (holds-ask '(quotedArg DiscordMessageFn 1 string) CPT))
  (is (holds-ask '(result DiscordMessageFn discord_message) CPT))
  (is (holds-ask '(functionCorrespondingPredicate DiscordMessageFn discordMessageOf) CPT))
  (is (holds-ask '(quotedArg discordMessageOf 1 string) CPT))
  (is (holds-ask '(arg discordMessageOf 2 discord_message) CPT))
  (is (holds-ask '(functional discordMessageOf) CPT))
  (testing "discordMessageClaims is typed and marked as agentClaims is"
    (is (holds-ask '(binary_predicate discordMessageClaims) CPT))
    (is (holds-ask '(arg discordMessageClaims 1 discord_message) CPT))
    (is (holds-ask '(arg discordMessageClaims 2 thing) CPT))
    (is (following? 'discordMessageClaims))))

(tu/deftest-kb a-message-claims-a-sentex-by-handle
  (tu/with-terms [CxDesk Speaker]
    (desk! kb CxDesk)
    (let [claim   (v/assert kb (list 'human Speaker) CxDesk)
          target  (sx/sentex-handle claim)
          receipt (list 'discordMessageClaims message target)]
      (v/assert kb receipt CxDesk)
      (is (holds-ask receipt CxDesk) "the receipt asked back ground")
      (is (= [message]
             (mapv #(v/term-expression kb (get % '?m))
                   (v/query kb (list 'discordMessageClaims '?m target) CxDesk)))
          "the claim's handle bound, the message it came from answered")
      (is (= [{'?s target}]
             (vec (v/query kb (list 'discordMessageClaims message '?s) CxDesk)))
          "the message bound, the claim it carries answered")
      (is (holds-ask (list 'discord_message message) CxDesk)
          "the function's result type, not an asserted membership")
      (v/retract! kb claim)
      (is (not (holds-ask receipt CxDesk))
          "target_following_predicate: retracting the claim takes its receipt with it"))))

(tu/deftest-kb a-snowflake-is-a-string
  (tu/with-terms [CxDesk Speaker]
    (desk! kb CxDesk)
    (let [claim (v/assert kb (list 'human Speaker) CxDesk)]
      (is (= [:quoted-arg-type]
             (problem-types (list 'discordMessageClaims '(DiscordMessageFn 175928847299117063)
                                  (sx/sentex-handle claim))
                            CxDesk))
          "a snowflake given as a number, not the decimal string quotedArg asks for"))))
