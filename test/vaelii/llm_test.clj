;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.llm-test
  "The pluggable LLM that proposes KB edits (`vaelii.impl.llm.*`).

  Every test here runs against the **offline stub provider**, so the suite needs no
  API key and opens no socket.  What is under test is the pipeline around the model,
  not the model: the generated tool schemas, the generated system prompt, batch
  parsing, the deterministic critic and its typed rejections, the bounded repair loop
  — and the invariant the whole design rests on, that a proposal never reaches storage
  without an explicit apply."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.llm.anthropic :as anthropic]
            [vaelii.impl.llm.prompt :as prompt]
            [vaelii.impl.llm.protocol :as proto]
            [vaelii.impl.llm.session :as session]
            [vaelii.impl.llm.stub :as stub]
            [vaelii.impl.llm.tools :as tools]
            [vaelii.impl.serve :as serve]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- tool schemas are generated from serve/ops --------------------------

(deftest read-ops-are-the-read-subset-of-the-daemon-op-table
  (let [reads (set (tools/read-ops))]
    (is (seq reads))
    (is (every? (set (keys serve/ops)) reads)
        "every exposed tool names an op the daemon already serves")
    (is (empty? (filter tools/write-ops reads))
        "no declared write is exposed")
    (testing "the writes are named and reachable through serve, just not as tools"
      (doseq [w tools/write-ops]
        (is (contains? serve/ops w) (str w " is declared a write but serve does not serve it"))
        (is (not (contains? reads w)))))))

(deftest no-write-is-reachable-as-a-tool
  (testing "the write ops have no tool name that dispatches"
    (doseq [w tools/write-ops]
      (is (nil? (tools/op-of (tools/tool-name w)))
          (str (tools/tool-name w) " must not resolve to an op"))))
  (testing "and a made-up write tool is simply unknown"
    (is (nil? (tools/op-of "kb_assert")))
    (is (= false (:ok (tools/call (tu/fresh) "kb_assert" {"sentence" "(dog Muffet)"}))))))

(deftest schemas-are-well-formed-and-stable
  (let [ss (tools/schemas)]
    (is (= (count (tools/read-ops)) (count ss)))
    (doseq [s ss]
      (is (re-matches #"[a-zA-Z0-9_-]{1,128}" (get s "name"))
          (str "tool name is not a legal identifier: " (get s "name")))
      (is (not (str/blank? (get s "description"))))
      (let [schema (get s "input_schema")]
        (is (= "object" (get schema "type")))
        (is (false? (get schema "additionalProperties")))
        (is (every? (set (keys (get schema "properties"))) (get schema "required"))
            (str (get s "name") ": a required parameter is missing from properties")))
      (when (get s "strict")
        (is (= (set (keys (get (get s "input_schema") "properties")))
               (set (get (get s "input_schema") "required")))
            (str (get s "name") ": strict claimed with an optional parameter"))))
    (is (= ss (tools/schemas)) "generation is deterministic"))
  (testing "narrowing"
    (is (= ["kb_sentexes_matching"] (mapv #(get % "name") (tools/schemas {:only #{:sentexes-matching}}))))
    (is (not (contains? (set (mapv #(get % "name") (tools/schemas {:exclude #{:sentexes-matching}})))
                        "kb_sentexes_matching")))))

(deftest tool-names-round-trip
  (doseq [op (tools/read-ops)]
    (is (= op (tools/op-of (tools/tool-name op))) (str "round trip failed for " op)))
  (testing "the ? ops stay distinct from their plain twins"
    (is (not= (tools/tool-name :ask) (tools/tool-name :ask?)))))

(tu/deftest-kb tool-calls-reach-the-kb
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (testing "a query returns the stored sentence"
      (let [{:keys [ok result]} (tools/call kb "kb_sentexes_matching" {"sentence" (pr-str (list dog '?x))})]
        (is ok)
        (is (str/includes? result (str Muffet)))))
    (testing "an integer parameter arrives as an integer"
      (let [h (v/handle-of kb (list dog Muffet) 'UniverseContext)
            {:keys [ok result]} (tools/call kb "kb_in_p" {"handle" h})]
        (is ok)
        (is (= "true" result))))
    (testing "a taxonomic read"
      (let [{:keys [ok result]} (tools/call kb "kb_isa_p" {"x" (str Muffet) "t" (str animal)})]
        (is ok)
        (is (= "true" result))))
    (testing "a failing call is reported, not thrown"
      (let [{:keys [ok error]} (tools/call kb "kb_sentexes_matching" {"sentence" "(unbalanced"})]
        (is (false? ok))
        (is (some? error))))
    (testing "results are bounded"
      (let [{:keys [result]} (tools/call kb "kb_terms" {} {:max-result-chars 20})]
        (is (str/includes? result "truncated"))))))

;; ---- the system prompt is generated from the KB -------------------------

(tu/deftest-kb system-prompt-reads-the-live-kb
  (tu/with-terms [dog animal Muffet StoryContext]
    (let [before (prompt/system-prompt kb)]
      (is (not (str/includes? before (str dog))))
      (v/assert kb (list 'genl dog animal) 'UniverseContext)
      (v/assert kb (list 'genlContext StoryContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list dog Muffet) StoryContext)
      (let [after (prompt/system-prompt kb)]
        (is (str/includes? after (str dog)) "a new type reaches the prompt")
        (is (str/includes? after (str StoryContext)) "a new context reaches the prompt")
        (is (str/includes? after "Naming invariants"))
        (is (str/includes? after ":add"))
        (is (= after (prompt/system-prompt kb)) "generation is deterministic")
        (is (not= before after))))))

(tu/deftest-kb system-prompt-carries-argisa-and-disjointness
  (tu/with-terms [dog cat parentOf Muffet]
    (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
    (v/assert kb (list 'argIsa parentOf 1 dog) 'UniverseContext)
    (let [p (prompt/system-prompt kb)]
      (is (str/includes? p "Disjointness"))
      (is (str/includes? p (str dog)))
      (is (str/includes? p (str parentOf)))
      (is (str/includes? p (str "1:`" dog "`")) "argIsa reaches the predicate line"))))

;; ---- parsing a proposed batch -------------------------------------------

(deftest parse-batch-reads-the-last-fenced-block
  (testing "a fenced edn block"
    (is (= {:add [] :remove []}
           (:batch (session/parse-batch "here you go\n\n```edn\n{:add [] :remove []}\n```")))))
  (testing "the last block wins — a model often shows a draft first"
    (is (= {:add [['(dog Muffet) 'WellContext]] :remove []}
           (:batch (session/parse-batch
                    (str "draft:\n```edn\n{:add [] :remove []}\n```\n"
                         "final:\n```edn\n{:add [[(dog Muffet) WellContext]]}\n```"))))))
  (testing "an unfenced map still parses"
    (is (= {:add [] :remove [7]} (:batch (session/parse-batch "{:remove [7]}")))))
  (testing "failures are reported, never thrown"
    (is (:error (session/parse-batch "```edn\n{:add [[( \n```")))
    (is (:error (session/parse-batch "```edn\n[1 2 3]\n```")))
    (is (:error (session/parse-batch "```edn\n{:add 5}\n```")))
    (is (:error (session/parse-batch "")))))

(deftest parse-batch-cannot-evaluate-code
  (testing "EDN has no reader-eval, so a model's output is inert data"
    (is (:error (session/parse-batch "```edn\n#=(java.lang.System/exit 1)\n```")))))

;; ---- the deterministic critic: typed rejections -------------------------

(tu/deftest-kb a-bad-predicate-name-is-a-naming-rejection
  (tu/with-terms [Muffet]
    (let [rs (session/check-batch kb {:add [[(list 'BadFunctor Muffet) 'UniverseContext]]
                                      :remove []})]
      (is (= 1 (count rs)))
      (is (= :naming (:type (first rs))))
      (is (= :add (:in (first rs))))
      (is (str/includes? (:message (first rs)) "functor")))))

(tu/deftest-kb a-non-ground-fact-is-a-not-ground-rejection
  (tu/with-terms [mortal]
    (let [rs (session/check-batch kb {:add [[(list mortal '?x) 'UniverseContext]] :remove []})]
      (is (= 1 (count rs)))
      (is (= :not-ground (:type (first rs)))))))

(tu/deftest-kb a-disjoint-clash-is-a-disjoint-rejection
  (tu/with-terms [dog cat Muffet]
    (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [rs (session/check-batch kb {:add [[(list cat Muffet) 'UniverseContext]] :remove []})]
      (is (= 1 (count rs)))
      (is (= :disjoint (:type (first rs))))))
  (testing "the critic did not store the entry it rejected"
    (tu/with-terms [dog cat Muffet]
      (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
      (session/check-batch kb {:add [[(list cat Muffet) 'UniverseContext]] :remove []})
      (is (nil? (v/handle-of kb (list cat Muffet) 'UniverseContext))
          "checking must not write"))))

(tu/deftest-kb an-argisa-clash-is-an-arg-type-rejection
  (tu/with-terms [dog cat likes Muffet Whiskers]
    (v/assert kb (list 'genl dog 'thing) 'UniverseContext)
    (v/assert kb (list 'genl cat 'thing) 'UniverseContext)
    (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
    (v/assert kb (list 'argIsa likes 1 dog) 'UniverseContext)
    (v/assert kb (list cat Whiskers) 'UniverseContext)
    (let [rs (session/check-batch kb {:add [[(list likes Whiskers Muffet) 'UniverseContext]]
                                      :remove []})]
      (is (= 1 (count rs)))
      (is (= :arg-type (:type (first rs)))))))

(tu/deftest-kb malformed-entries-and-handles-are-rejected
  (testing "an entry that is not [sentence context]"
    (is (= :shape (:type (first (session/check-batch kb {:add ['(dog Muffet)] :remove []}))))))
  (testing "a context that is not a symbol"
    (is (= :shape (:type (first (session/check-batch
                                 kb {:add [['(dog Muffet) "WellContext"]] :remove []}))))))
  (testing "a removal naming no stored sentex"
    (let [rs (session/check-batch kb {:add [] :remove [999999]})]
      (is (= :unknown-handle (:type (first rs))))
      (is (= :remove (:in (first rs))))))
  (testing "a removal naming a stored one is fine"
    (tu/with-terms [dog Muffet]
      (let [h (v/assert kb (list dog Muffet) 'UniverseContext)]
        (is (empty? (session/check-batch kb {:add [] :remove [h]})))))))

(tu/deftest-kb a-well-formed-batch-has-no-rejections
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (is (empty? (session/check-batch kb {:add [[(list dog Muffet) 'UniverseContext]]
                                         :remove []})))))

;; ---- the repair loop ----------------------------------------------------

(tu/deftest-kb the-loop-repairs-a-rejected-batch
  (tu/with-terms [dog Muffet]
    (let [p (stub/provider
             {:script [{:batch {:add [[(list 'BadFunctor Muffet) 'UniverseContext]] :remove []}}
                       {:batch {:add [[(list dog Muffet) 'UniverseContext]] :remove []}}]})
          result (session/propose kb {:message "add Muffet as a dog" :provider p})]
      (is (= :ok (:status result)))
      (is (= 2 (:attempts result)) "one rejected batch, one accepted")
      (is (= {:add [[(list dog Muffet) 'UniverseContext]] :remove []} (:batch result)))
      (testing "the critic's typed verdict is what was fed back"
        (is (str/includes? (stub/last-user-text p) ":naming"))
        (is (str/includes? (stub/last-user-text p) "BadFunctor"))))))

(tu/deftest-kb the-loop-gives-up-cleanly-when-repair-fails
  (tu/with-terms [Muffet]
    (let [bad {:batch {:add [[(list 'BadFunctor Muffet) 'UniverseContext]] :remove []}}
          p (stub/provider {:script [bad bad bad bad bad] :default (:batch bad)})
          result (session/propose kb {:message "break it" :provider p :max-repairs 2})]
      (is (= :invalid (:status result)) "a stubborn model ends in a report, not a throw")
      (is (= 3 (:attempts result)) "the initial proposal plus :max-repairs retries")
      (is (= :naming (:type (first (:rejections result)))))
      (is (some? (:batch result)) "the rejected batch is still handed back for review"))))

(tu/deftest-kb an-unparseable-answer-is-repaired-then-reported
  (let [p (stub/provider {:script ["I have no idea what you mean." "still nothing"]
                          :default {:stop-reason "end_turn" :model "vaelii-stub"
                                    :content [{:type :text :text "nope"}] :usage {}}})
        result (session/propose kb {:message "?" :provider p :max-repairs 1})]
    (is (= :unparseable (:status result)))
    (is (= :unparseable (:type (first (:rejections result)))))))

(tu/deftest-kb a-refusal-is-detected-before-the-content-is-read
  (let [p (stub/provider {:script [{:stop-reason "refusal"
                                    :stop-details {"type" "refusal" "category" "cyber"}
                                    :model "vaelii-stub" :content [] :usage {}}]})
        result (session/propose kb {:message "do something disallowed" :provider p})]
    (is (= :refused (:status result)))
    (is (= "cyber" (get (:stop-details result) "category")))
    (is (nil? (:batch result)) "no batch is invented out of an empty content array")))

(tu/deftest-kb the-loop-runs-read-tools-then-answers
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [p (stub/provider
             {:script [{:tool "kb_types_of" :input {"x" (str Muffet)} :prose "checking first"}
                       {:batch {:add [] :remove []}}]})
          result (session/propose kb {:message "what is Muffet?" :provider p})]
      (is (= :ok (:status result)))
      (is (= 1 (:tool-calls result)))
      (is (= 2 (:turns result)))
      (testing "the tool result went back as a tool_result block naming its call"
        (let [msgs (:messages result)
              tr (->> msgs (mapcat :content) (filter map?)
                      (filter #(= :tool-result (:type %))) first)]
          (is (some? tr))
          (is (str/includes? (:content tr) (str dog))))))))

(tu/deftest-kb the-turn-cap-stops-a-spinning-model
  (let [p (stub/provider {:default {:stop-reason "tool_use" :model "vaelii-stub"
                                    :content [{:type :tool-use :id "t" :name "kb_contexts"
                                               :input {}}]
                                    :usage {}}})
        result (session/propose kb {:message "spin" :provider p :max-turns 4})]
    (is (= :exhausted (:status result)))
    (is (= 4 (:turns result)))))

;; ---- streaming ----------------------------------------------------------

(tu/deftest-kb streaming-yields-deltas-and-the-same-result
  (tu/with-terms [dog Muffet]
    (let [events (atom [])
          batch {:add [[(list dog Muffet) 'UniverseContext]] :remove []}
          p (stub/provider {:script [{:batch batch}]})
          result (session/propose kb {:message "add it" :provider p
                                      :on-event #(swap! events conj %)})]
      (is (= :ok (:status result)))
      (is (= batch (:batch result)))
      (is (seq (filter #(= :text-delta (:type %)) @events)) "text arrived incrementally")
      (is (= 1 (count (filter #(= :done (:type %)) @events)))))))

;; ---- the write boundary -------------------------------------------------

(tu/deftest-kb a-proposal-is-never-applied-without-an-explicit-apply
  (tu/with-terms [dog Muffet]
    (let [before (tu/sentex-ids kb)
          batch {:add [[(list dog Muffet) 'UniverseContext]] :remove []}
          p (stub/provider {:script [{:batch batch}]})
          proposal (session/propose kb {:message "add Muffet" :provider p})]
      (is (= :ok (:status proposal)))
      (is (= before (tu/sentex-ids kb))
          "proposing stored nothing — the model has no write path")
      (is (nil? (v/handle-of kb (list dog Muffet) 'UniverseContext)))
      (testing "the explicit apply is what writes"
        (let [applied (session/apply-proposal! kb proposal)]
          (is (= 1 (count (:added (:result applied)))))
          (is (some? (v/handle-of kb (list dog Muffet) 'UniverseContext)))
          (is (empty? (:violations applied))))))))

(tu/deftest-kb apply-refuses-a-proposal-the-critic-rejected
  (tu/with-terms [Muffet]
    (let [bad {:batch {:add [[(list 'BadFunctor Muffet) 'UniverseContext]] :remove []}}
          p (stub/provider {:script [bad bad bad] :default (:batch bad)})
          proposal (session/propose kb {:message "x" :provider p :max-repairs 1})]
      (is (= :invalid (:status proposal)))
      (is (thrown? clojure.lang.ExceptionInfo (session/apply-proposal! kb proposal)))
      (is (= :llm-not-applicable
             (try (session/apply-proposal! kb proposal)
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))))

(tu/deftest-kb apply-round-trips-a-removal
  (tu/with-terms [dog Muffet]
    (let [h (v/assert kb (list dog Muffet) 'UniverseContext)
          p (stub/provider {:script [{:batch {:add [] :remove [h]}}]})
          proposal (session/propose kb {:message "drop it" :provider p})]
      (is (= :ok (:status proposal)))
      (is (some? (v/handle-of kb (list dog Muffet) 'UniverseContext)) "still there after proposing")
      (session/apply-proposal! kb proposal)
      (is (nil? (v/handle-of kb (list dog Muffet) 'UniverseContext))))))

;; ---- the default provider is offline ------------------------------------

(tu/deftest-kb the-default-provider-needs-no-credential
  (let [result (session/propose kb {:message "anything"})]
    (is (= :ok (:status result)))
    (is (= {:add [] :remove []} (:batch result))
        "with no provider installed the stub proposes nothing, deterministically")))

;; ---- the real backend, offline -----------------------------------------
;; Encoding and decoding are pure, so the parts most likely to be wrong are tested
;; without a credential and without a socket.

(deftest the-request-body-omits-the-rejected-sampling-parameters
  (let [b (#'anthropic/body {:model "claude-opus-5"
                             :system [{:text "stable prefix" :cache? true}]
                             :messages [{:role "user" :content "hi"}]
                             :tools (tools/schemas {:only #{:sentexes-matching}})
                             :effort "high"}
                            {:stream? false})]
    (testing "temperature / top_p / top_k are rejected by this model family"
      (is (not-any? (set (keys b)) ["temperature" "top_p" "top_k"])))
    (testing "thinking takes no token budget — depth is effort"
      (is (nil? (get b "thinking")))
      (is (= {"effort" "high"} (get b "output_config"))))
    (testing "the stable prefix carries the cache breakpoint, the user turn does not"
      (is (= {"type" "ephemeral"} (get-in b ["system" 0 "cache_control"])))
      (is (= "hi" (get-in b ["messages" 0 "content"]))))
    (is (= "claude-opus-5" (get b "model")))
    (is (pos? (get b "max_tokens")))
    (is (= 1 (count (get b "tools"))))))

(deftest the-request-body-opts-into-a-refusal-fallback
  (let [b (#'anthropic/body {:messages []} {:stream? false})]
    (is (= "default" (get b "fallbacks")))
    (is (= [anthropic/fallback-beta] (#'anthropic/betas-for {:messages []}))))
  (testing "and it can be dropped for an org that has not enabled the beta"
    (let [b (#'anthropic/body {:messages [] :fallbacks nil} {:stream? false})]
      (is (nil? (get b "fallbacks")))
      (is (nil? (#'anthropic/betas-for {:messages [] :fallbacks nil}))))))

(deftest streaming-asks-for-more-room-than-a-single-response
  (is (< (get (#'anthropic/body {:messages []} {:stream? false}) "max_tokens")
         (get (#'anthropic/body {:messages []} {:stream? true}) "max_tokens")))
  (is (true? (get (#'anthropic/body {:messages []} {:stream? true}) "stream"))))

(deftest an-oauth-credential-uses-bearer-and-the-oauth-beta
  (let [api (#'anthropic/headers {:kind :api-key :value "test-value"} [])
        oauth (#'anthropic/headers {:kind :bearer :value "test-value"} [])]
    (is (= "test-value" (get api "x-api-key")))
    (is (nil? (get api "authorization")))
    (is (= "Bearer test-value" (get oauth "authorization")))
    (is (nil? (get oauth "x-api-key")))
    (is (str/includes? (get oauth "anthropic-beta") "oauth-2025-04-20"))
    (is (= anthropic/api-version (get api "anthropic-version")))))

(deftest a-refusal-decodes-without-inventing-content
  (let [r (anthropic/parse-response
           {"stop_reason" "refusal"
            "stop_details" {"type" "refusal" "category" "cyber"}
            "content" []})]
    (is (proto/refused? r))
    (is (= [] (:content r)))
    (is (= "" (proto/text r)))))

(deftest tool-use-and-thinking-blocks-round-trip
  (let [r (anthropic/parse-response
           {"stop_reason" "tool_use"
            "content" [{"type" "thinking" "thinking" "hmm" "signature" "sig"}
                       {"type" "text" "text" "checking"}
                       {"type" "tool_use" "id" "toolu_1" "name" "kb_sentexes_matching"
                        "input" {"sentence" "(dog ?x)"}}]})]
    (is (= "checking" (proto/text r)))
    (is (= 1 (count (proto/tool-uses r))))
    (is (= "kb_sentexes_matching" (:name (first (proto/tool-uses r)))))
    (testing "each block keeps its original JSON, so it echoes back unedited"
      (is (= "sig" (get-in (:content r) [0 :raw "signature"])))
      (is (= {"type" "text" "text" "checking"} (#'anthropic/encode-block (nth (:content r) 1)))))))

(deftest sse-frames-reassemble-into-the-same-response-shape
  (let [events (atom [])
        r (#'anthropic/collect
           [{"type" "message_start" "message" {"model" "claude-opus-5" "usage" {"input_tokens" 12}}}
            {"type" "content_block_start" "index" 0
             "content_block" {"type" "thinking" "thinking" ""}}
            {"type" "content_block_delta" "index" 0
             "delta" {"type" "thinking_delta" "thinking" "weighing it"}}
            {"type" "content_block_delta" "index" 0
             "delta" {"type" "signature_delta" "signature" "sig-abc"}}
            {"type" "content_block_stop" "index" 0}
            {"type" "content_block_start" "index" 1 "content_block" {"type" "text" "text" ""}}
            {"type" "content_block_delta" "index" 1 "delta" {"type" "text_delta" "text" "one "}}
            {"type" "content_block_delta" "index" 1 "delta" {"type" "text_delta" "text" "two"}}
            {"type" "content_block_stop" "index" 1}
            {"type" "content_block_start" "index" 2
             "content_block" {"type" "tool_use" "id" "toolu_9" "name" "kb_types_of" "input" {}}}
            {"type" "content_block_delta" "index" 2
             "delta" {"type" "input_json_delta" "partial_json" "{\"x\":"}}
            {"type" "content_block_delta" "index" 2
             "delta" {"type" "input_json_delta" "partial_json" "\"Muffet\"}"}}
            {"type" "content_block_stop" "index" 2}
            {"type" "message_delta" "delta" {"stop_reason" "tool_use"} "usage" {"output_tokens" 30}}]
           #(swap! events conj %))]
    (is (= "one two" (proto/text r)))
    (is (= "tool_use" (:stop-reason r)))
    (is (= {"x" "Muffet"} (:input (first (proto/tool-uses r)))) "partial json reassembles")
    (testing "the signature arrives as its own delta and must ride back out"
      (is (= "sig-abc" (get-in (:content r) [0 :raw "signature"])))
      (is (= "weighing it" (get-in (:content r) [0 :raw "thinking"]))))
    (testing "blocks are ordered by index, whatever order the frames folded in"
      (is (= [:thinking :text :tool-use] (mapv :type (:content r)))))
    (is (= 2 (count (filter #(= :text-delta (:type %)) @events))))))

(deftest a-missing-credential-is-a-typed-refusal-not-a-crash
  (let [outcome (try (anthropic/provider) :built
                     (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))]
    ;; Machine-dependent by nature — the point is that *both* outcomes are clean:
    ;; a reachable credential builds a provider, an absent one is a typed refusal
    ;; a caller can branch on, never a NullPointerException from a header.
    (is (= (if (anthropic/available?) :built :llm-no-credential) outcome))))

(deftest the-protocol-reads-stop-reason-before-content
  (is (proto/refused? {:stop-reason "refusal" :content []}))
  (is (not (proto/refused? {:stop-reason "end_turn" :content []})))
  (is (= "" (proto/text {:stop-reason "refusal" :content []})))
  (is (= "ab" (proto/text {:content [{:type :text :text "a"}
                                     {:type :thinking :text "zzz"}
                                     {:type :text :text "b"}]}))))

;; ---- the suite is hermetic, and a mark is what says so ------------------
;; Everything the LLM pipeline does is tested against the offline stub, so a test that
;; talks to a real host is the exception — and `lein test` must not become the thing that
;; dials one.  Two gates hold that, and they are independent on purpose: the `^:llm` mark
;; keeps such a test out of `:default` and `:all` (project.clj), and `tu/live-llm?` is the
;; consent to make the call at all.  Neither is worth much without the other, so this
;; checks they agree — over the source, because that is where a new test gets it wrong.

(def ^:private live-marker
  "What a test consulting the live gate looks like: `live-llm?` under any alias, or a
  namespace-local `live-model` helper that wraps it.

  The second half is a **convention this check depends on**: a helper sits between two
  tests, so a test that reaches the gate through one does not mention the gate in its own
  body.  A new live test must therefore either consult it directly or route through a
  helper called `live-model` — the roster test below is what makes a new marked test a
  visible change if it does neither.

  Anchored on the shape of a **call** — an open paren, then the name, then a close — and
  not on the bare name, so this does not match the prose around it or its own failure
  messages.  A scanner that flags its own source is worse than no scanner, since the way
  to make it green is to stop saying what it checks."
  #"\([\w.-]*/?live-llm\?\)|\(live-model\)")

(defn- top-level-starts
  "The index of every top-level form in a source file — a `(` in column zero."
  [src]
  (vec (keep-indexed (fn [i c] (when (and (= \( c) (or (zero? i) (= \newline (nth src (dec i)))))
                                 i))
                     src)))

(defn- test-forms
  "Every top-level `deftest` / `tu/deftest-kb` in a test file, as
  `[{:file :name :marked? :body} …]`.

  Split on column-zero openers rather than read, since what is under test is the **source**
  a reader edits: a mark dropped from the text is the failure mode, and `read`ing the file
  would resolve it away.  A body runs to the next **top-level form**, not to the next
  `deftest` — a helper defined between two tests belongs to neither, and taking it as part
  of the one before it is how this check first reported two tests that dial out and do not."
  [path]
  (let [src    (slurp path)
        starts (top-level-starts src)
        next-start (fn [at] (or (first (drop-while #(<= % at) starts)) (count src)))]
    (for [at starts
          :let [head (subs src at (min (count src) (+ at 200)))
                m (re-find #"^\((?:clojure\.test/)?(?:tu/)?deftest(?:-kb)?\s+((?:\^:\S+\s+)*)([^\s()]+)"
                           head)]
          :when m]
      (let [[_ marks nm] m]
        {:file path
         :name nm
         :marked? (boolean (re-find #"\^:llm\b" (str marks)))
         :body (subs src at (next-start at))}))))

(def ^:private all-tests
  (delay (mapcat test-forms
                 (->> (file-seq (io/file "test"))
                      (filter #(.isFile ^java.io.File %))
                      (map #(.getPath ^java.io.File %))
                      (filter #(str/ends-with? % "_test.clj"))
                      sort))))

(deftest a-test-that-can-reach-a-model-carries-the-llm-mark
  (is (seq @all-tests) "the scan found the test sources")
  (testing "a test consulting the live gate is one that would otherwise dial out, so it
            must be excluded from :default and :all by its mark"
    (doseq [{:keys [file name marked? body]} @all-tests
            :when (re-find live-marker body)]
      (is marked? (str file " / " name " reaches a live model without ^:llm"))))
  (testing "and the converse — a marked test that never consults the gate would run
            against a host on nothing but a selector, which is not consent"
    (doseq [{:keys [file name marked? body]} @all-tests
            :when marked?]
      (is (re-find live-marker body)
          (str file " / " name " is ^:llm but never checks tu/live-llm?")))))

(deftest the-marked-tests-are-the-ones-we-think-they-are
  (testing "a roster, so adding a live test is a visible change rather than a quiet one"
    (is (= #{"a-live-model-reports-what-it-can-do"
             "a-live-model-edits-a-selection"
             "a-live-model-streams-the-same-answer"
             "a-live-model-fleshes-out-a-page"
             "a-live-model-judges-what-the-kb-concluded"
             "the-four-fables-scored-against-their-hand-written-selves"}
           (set (map :name (filter :marked? @all-tests)))))))
