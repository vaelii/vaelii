;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.host.llm.protocol
  "The pluggable-model extension point: one protocol, two methods, and a provider-neutral
  request/response shape.

  Mirrors `vaelii.impl.types.solve/Solver` — a protocol plus a deterministic stub as the
  default, with the real backend reached only when a caller installs it.  So the
  suite, and a build with no API key and no network, run the whole pipeline against
  `vaelii.host.llm.stub` and never open a socket.

  **The shapes are the contract.**  A provider takes a `request` map and answers a
  `response` map; neither mentions HTTP, JSON, or any vendor field, so the session
  loop (`vaelii.host.llm.session`) is written once and runs against either provider.

  Request:

      {:model      \"claude-opus-5\"     ; provider-resolved when absent
       :system     [{:text \"…\" :cache? true} …]   ; blocks, in order
       :messages   [{:role \"user\"|\"assistant\" :content <string | [block …]}]
       :tools      [<tool schema> …]      ; vaelii.host.llm.tools/schemas
       :format     {…}                    ; a JSON schema decoding is constrained to
       :max-tokens 8192
       :effort     \"low\"|\"medium\"|\"high\"|\"xhigh\"|\"max\"
       :num-ctx    8192}                  ; window size; local providers only

  `:cache?` on a system block asks the provider to mark it as a cache breakpoint;
  the generated system prompt is a large stable prefix and the user's turn is the
  volatile part after it, which is exactly the shape prompt caching wants.

  **This list is the whole of what a provider reads.**  A provider ignores what it
  cannot express — `:cache?` is a no-op on Ollama, `:num-ctx` on Anthropic — but a key
  the list does not name is a key an implementer has no reason to look for, and a
  dropped constraint is invisible downstream: a turn that runs unconstrained answers in
  the same shape as one that does not.  So a key any path sends belongs here.

  Response:

      {:stop-reason  \"end_turn\"|\"tool_use\"|\"refusal\"|\"max_tokens\"|…
       :stop-details {…}                ; populated only on a refusal
       :content      [{:type :text     :text \"…\"}
                      {:type :tool-use :id \"…\" :name \"…\" :input {…}}
                      {:type :thinking :text \"…\"}]
       :model        \"…\"
       :usage        {…}}

  A **refusal is a successful answer with no content** — the caller must read
  `:stop-reason` before reading `:content`, so a provider never fabricates a text
  block to keep indexing code happy.  Assistant content is echoed back verbatim in
  the next request's `:messages`, so a provider may carry vendor-specific blocks
  through `:content` untouched as long as it can read its own back.")

(defprotocol Provider
  (complete [provider request]
    "Run one turn and return the whole response map.  Blocks until the turn ends.")
  (stream [provider request on-event]
    "Run one turn incrementally: call `(on-event ev)` for each event as it arrives,
    then return the same response map `complete` would have.  Events are
    `{:type :text-delta :text \"…\"}`, `{:type :block-start :block {…}}`,
    `{:type :block-stop}`, `{:type :done :response {…}}`.  A provider with no
    incremental transport may satisfy this by calling `complete` and emitting one
    `:text-delta` per text block — the contract is the return value, not the
    granularity."))

(defn text
  "The concatenated text of a response's text blocks — what the model actually
  wrote, with tool-use and thinking blocks dropped.  Empty on a refusal, which is
  why `:stop-reason` is the thing to branch on."
  [response]
  (->> (:content response)
       (filter #(= :text (:type %)))
       (map :text)
       (apply str)))

(defn tool-uses
  "The tool-use blocks of a response, in order."
  [response]
  (filterv #(= :tool-use (:type %)) (:content response)))

(defn refused?
  "Did the provider's safety classifiers decline this request?  A refusal is an
  ordinary successful call whose content is empty or partial, so this is the guard
  that must run before anything reads `:content`."
  [response]
  (= "refusal" (:stop-reason response)))
