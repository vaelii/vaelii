;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.discord-permissions-test
  "Discord channel identities, names and permission abilities in CxTra."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(tu/deftest-kb channel-functions-reify-typed-identities-and-happening-kinds
  (tu/with-terms [CxDesk Ann]
    (v/assert kb (list 'genlCx CxDesk 'CxTra) 'CxUniverse)
    (v/assert kb (list 'human Ann) CxDesk)
    (let [channel '(DiscordChannelFn "42")
          access (list 'ChannelViewFn channel)]
      (v/assert kb (list 'able Ann access) CxDesk)
      (is (boolean (v/genl? kb 'discord_channel 'communication_channel CxDesk)))
      (is (boolean (v/genl? kb 'communication_channel 'intangible CxDesk)))
      (is (boolean (v/genl? kb 'communication_channel 'aspatial CxDesk)))
      (is (boolean (v/genl? kb 'communication_channel 'acausal CxDesk)))
      (is (boolean (v/genl? kb 'communication_channel 'temporal CxDesk)))
      (is (seq (v/ask kb (list 'discord_channel channel) CxDesk)))
      (is (seq (v/ask kb (list 'communication_channel channel) CxDesk)))
      (is (seq (v/ask kb (list 'temporal channel) CxDesk)))
      (is (seq (v/ask kb (list 'aspatial channel) CxDesk)))
      (is (seq (v/ask kb (list 'acausal channel) CxDesk)))
      (is (seq (v/ask kb (list 'discordChannelOf "42" channel) CxDesk)))
      (is (seq (v/ask kb (list 'channelViewOf channel access) CxDesk)))
      (is (seq (v/ask kb (list 'genl access 'channel_view) CxDesk)))
      (is (seq (v/ask kb (list 'able Ann 'resource_access) CxDesk)))
      (testing "a channel permission does not grant reading"
        (is (empty? (v/ask kb (list 'able Ann 'read_access) CxDesk)))
        (is (empty? (v/ask kb (list 'able Ann (list 'ReadAccessFn channel)) CxDesk)))
        (v/assert kb (list 'able Ann (list 'ReadAccessFn channel)) CxDesk)
        (is (seq (v/ask kb (list 'able Ann 'read_access) CxDesk)))
        (is (seq (v/ask kb (list 'able Ann (list 'ReadAccessFn channel)) CxDesk)))))))

(tu/deftest-kb permission-and-channel-names-are-scoped-to-their-observation-instants
  (tu/with-terms [CxDesk Ann]
    (v/assert kb (list 'genlCx CxDesk 'CxTra) 'CxUniverse)
    (v/assert kb (list 'human Ann) CxDesk)
    (let [first-time (list 'CxTimeFn CxDesk '(InstantFn 2026 11 3 15 30 0))
          next-time (list 'CxTimeFn CxDesk '(InstantFn 2026 11 3 15 31 0))
          channel '(DiscordChannelFn "42")
          permission (list 'able Ann (list 'ChannelViewFn channel))]
      (v/assert kb permission first-time)
      (v/assert kb (list 'discordChannelName channel "workshop") first-time)
      (v/assert kb (list 'discordChannelName channel "cafe") next-time)
      (is (seq (v/ask kb permission first-time)))
      (is (empty? (v/ask kb permission next-time)))
      (is (empty? (v/ask kb permission CxDesk)))
      (is (seq (v/ask kb (list 'discordChannelName channel "workshop") first-time)))
      (is (empty? (v/ask kb (list 'discordChannelName channel "workshop") next-time)))
      (is (seq (v/ask kb (list 'discordChannelName channel "cafe") next-time)))
      (is (empty? (v/ask kb (list 'discordChannelName channel "cafe") first-time))))))

(tu/deftest-kb a-shared-name-does-not-equate-channel-identities
  (tu/with-terms [CxDesk]
    (v/assert kb (list 'genlCx CxDesk 'CxTra) 'CxUniverse)
    (is (seq (v/ask kb '(not (functional discordChannelName)) CxDesk)))
    (is (seq (v/ask kb '(not (functionalInArg discordChannelName 1)) CxDesk)))
    (let [one '(DiscordChannelFn "42")
          other '(DiscordChannelFn "43")]
      (v/assert kb (list 'discordChannelName one "general") CxDesk)
      (v/assert kb (list 'discordChannelName other "general") CxDesk)
      (v/assert kb (list 'discordChannelName one "alias") CxDesk)
      (is (= 2 (count (v/ask kb '(discordChannelName ?channel "general") CxDesk))))
      (is (empty? (v/ask kb (list 'equals one other) CxDesk)))
      (is (seq (v/ask kb (list 'discordChannelName one "alias") CxDesk)))
      (is (empty? (v/ask kb (list 'discordChannelName other "alias") CxDesk))))))

(tu/deftest-kb account-use-is-many-to-many-and-does-not-grant-channel-permission
  (tu/with-terms [CxDesk Ann Bo]
    (v/assert kb (list 'genlCx CxDesk 'CxTra) 'CxUniverse)
    (is (seq (v/ask kb '(not (functional discordAccountId)) CxDesk)))
    (is (seq (v/ask kb '(not (functionalInArg discordAccountId 1)) CxDesk)))
    (doseq [person [Ann Bo]] (v/assert kb (list 'human person) CxDesk))
    (doseq [[person account] [[Ann "80"] [Ann "81"] [Bo "80"]]]
      (v/assert kb (list 'discordAccountId person account) CxDesk))
    (is (= #{"80" "81"} (set (map #(get % '?account)
                                  (v/ask kb (list 'discordAccountId Ann '?account) CxDesk)))))
    (is (= #{Ann Bo} (set (map #(get % '?person)
                               (v/ask kb '(discordAccountId ?person "80") CxDesk)))))
    (is (empty? (v/ask kb (list 'equals Ann Bo) CxDesk)))
    (is (empty? (v/ask kb (list 'able Ann 'channel_view) CxDesk)))
    (is (empty? (v/ask kb (list 'not (list 'able Ann 'channel_view)) CxDesk)))))
