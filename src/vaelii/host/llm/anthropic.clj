;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.llm.anthropic
  "The real backend: the Anthropic Messages API over raw HTTP.

  There is no official Anthropic SDK for Clojure, so raw HTTP is the supported path —
  and it adds no work here, because the repo already carries both halves: `cheshire`
  for JSON and JDK `java.net.http`, which `vaelii.host.client` already speaks to the
  vaelii daemon.  This namespace mirrors that one: an explicit connection handle, no
  global state, **no new dependency**.

  Reached only when a caller installs it (`vaelii.host.llm.stub` is the default), so a
  build with no credential and no network never loads a socket.

  Request shape notes, because several of them are required:

  * **`temperature` / `top_p` / `top_k` are rejected** on this model family — they are
    never sent, and steering happens in the prompt instead.
  * **Thinking is on by default** and takes no token budget; depth is set with
    `output_config.effort`.  `:thinking-display \"summarized\"` opts into a readable
    summary (the default omits the text).
  * A **refusal is HTTP 200** with `stop_reason: \"refusal\"` and empty or partial
    content, so `parse-response` never fabricates a text block and the session loop
    branches on `:stop-reason` before touching `:content`.
  * The generated system prompt is a large stable prefix, so its last block carries a
    `cache_control` breakpoint; the user's turn sits after it.  The minimum cacheable
    prefix on `claude-opus-5` is 512 tokens — a short prompt simply will not cache,
    with no error.
  * `fallbacks` is sent by default so a policy decline is re-served rather than
    returned as a dead turn.  It rides a beta header; pass `{:fallbacks nil}` to drop
    both if the org has not enabled it.
  * **`:format` is structured outputs** — a JSON schema, sent as `output_config.format`.
    Ollama takes the same schema under its own `format` key, so one neutral request
    constrains decoding on either provider.  The paths that carry one are the tool-free
    ones; the `propose` loop sends tools and reads a fenced block instead.

  **Credentials are resolved from the environment, never hardcoded and never logged**
  — see `credentials`."
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [vaelii.host.llm.http :as http]
            [vaelii.host.llm.protocol :as proto])
  (:import [java.io BufferedReader InputStream InputStreamReader]
           [java.lang ProcessBuilder$Redirect]
           [java.net URI]
           [java.net.http HttpClient HttpClient$Builder HttpRequest HttpRequest$Builder
            HttpRequest$BodyPublishers HttpResponse HttpResponse$BodyHandlers]
           [java.nio.charset StandardCharsets]
           [java.time Duration]))

(def default-model
  "The model this backend talks to unless told otherwise."
  "claude-opus-5")

(def api-version "2023-06-01")

(def fallback-beta
  "Beta flag for the scalar `fallbacks: \"default\"` form — routes a policy decline to
  Anthropic's recommended substitute model by refusal category."
  "server-side-fallback-2026-07-01")

;; ---- deadlines ----------------------------------------------------------

(def ^:private endpoint
  "How this provider's far end is named — in a message a reader sees, and in the
  deadline thread's title.  `vaelii.host.llm.http` takes it; it is the whole of what
  distinguishes this namespace's transport from the Ollama one's."
  {:label "the Anthropic API" :slug "anthropic"})

;; ---- credentials --------------------------------------------------------

(def ^:private cli-timeout-ms
  "How long `ant auth print-credentials` gets before it is killed.  `available?` reaches
  it and a request thread calls `available?` to choose between this backend and the stub,
  so a CLI that wedges must not wedge the request.  Killed rather than abandoned: the
  answer is then \"no credential\", which is what an absent CLI already answers."
  5000)

(defn- clean
  "A credential as read from the environment: trimmed, and nil when it holds nothing.
  A `.env` file ending in CRLF and a `$(cat key)` in a shell that keeps the newline are
  the two ways a stray character rides in.  Trimming is **not** the guarantee — a control
  character mid-string still reaches the JDK, and `request-builder` is what refuses that —
  it keeps the ordinary case from getting there at all."
  [s]
  (not-empty (str/trim (str s))))

(defn- ant-cli-token
  "A short-lived access token from an `ant auth login` profile, or nil.  Shelling out
  is the documented way to hand an OAuth profile to a raw-HTTP caller; the token is
  returned, never printed, and a CLI that has not answered within `cli-timeout-ms` is
  killed rather than waited on — this runs on a request thread.

  The child and the deadline thread are given back on **every** exit, not only the one
  that read a token: a read that throws would otherwise leave a subprocess running and a
  thread sleeping out the full `cli-timeout-ms` behind a call that has already answered
  nil.  And an interrupt is put back rather than swallowed — this runs on a request
  thread, and a cancelled job that lost its interrupt here goes on to its next report."
  []
  (try
    (let [^java.util.List argv ["ant" "auth" "print-credentials" "--access-token"]
          ^ProcessBuilder pb (ProcessBuilder. argv)
          _ (.redirectError pb ProcessBuilder$Redirect/DISCARD)
          ^Process proc (.start pb)
          ^Thread killer (http/watchdog endpoint cli-timeout-ms
                                        #(.destroyForcibly ^Process proc))]
      (try
        (let [out  (slurp (.getInputStream proc))
              exit (.waitFor proc)]
          (when (zero? exit) (clean out)))
        (finally
          (.interrupt killer)
          (.destroyForcibly proc))))
    (catch InterruptedException _
      (.interrupt (Thread/currentThread))
      nil)
    (catch Exception _ nil)))

(defn credentials
  "The credential to authenticate with, as `{:kind :api-key|:bearer :value \"…\"}`, or
  nil when none is reachable.

  Resolution order matches the official SDKs: `ANTHROPIC_API_KEY`, then
  `ANTHROPIC_AUTH_TOKEN`, then an `ant auth login` profile via the `ant` CLI.  **An
  unset `ANTHROPIC_API_KEY` does not mean there is no credential** — an active OAuth
  profile is enough, and it authenticates with `Authorization: Bearer` plus the OAuth
  beta header rather than `x-api-key`.

  The value is a secret: it is returned for the caller to hand straight to a header
  and is never logged, printed, or put in an exception message.  `request-builder` is
  what holds that last clause where the JDK would not."
  []
  (or (when-let [k (clean (System/getenv "ANTHROPIC_API_KEY"))]
        {:kind :api-key :value k})
      (when-let [t (clean (System/getenv "ANTHROPIC_AUTH_TOKEN"))]
        {:kind :bearer :value t})
      (when-let [t (ant-cli-token)]
        {:kind :bearer :value t})))

(defn available?
  "Is a credential reachable?  The gate a caller uses to decide between this backend
  and the stub."
  []
  (some? (credentials)))

;; ---- request encoding ---------------------------------------------------

(defn- encode-block
  "One neutral content block -> the API's JSON shape.  A block parsed from a response
  carries its original JSON under `:raw`, which is echoed back **unchanged** — the API
  rejects an edited thinking block, and a vendor block type this namespace does not
  model still round-trips."
  [block]
  (or (:raw block)
      (case (:type block)
        :text        {"type" "text" "text" (:text block)}
        :tool-result (cond-> {"type" "tool_result"
                              "tool_use_id" (:tool-use-id block)
                              "content" (:content block)}
                       (:error? block) (assoc "is_error" true))
        :tool-use    {"type" "tool_use" "id" (:id block)
                      "name" (:name block) "input" (or (:input block) {})}
        (throw (ex-info (str "cannot encode content block of type " (pr-str (:type block))
                             " — want :text, :tool-use or :tool-result, or a block"
                             " carrying its original JSON under :raw")
                        {:type :llm-encode :block-type (:type block)})))))

(defn- encode-message [{:keys [role content]}]
  {"role" role
   "content" (if (string? content) content (mapv encode-block content))})

(defn- encode-system
  "System blocks, with a `cache_control` breakpoint on each block flagged `:cache?`.
  The generated prompt is the stable prefix, so caching it is the whole point; the
  volatile user turn is in `messages`, after the breakpoint."
  [blocks]
  (mapv (fn [{:keys [text cache?]}]
          (cond-> {"type" "text" "text" text}
            cache? (assoc "cache_control" {"type" "ephemeral"})))
        blocks))

(defn- body
  [{:keys [model system messages tools max-tokens effort thinking-display fallbacks]
    fmt :format
    :or {fallbacks "default"}}
   {:keys [stream?]}]
  ;; `:effort` and `:format` are two keys of one object, so one binding builds both: a
  ;; second `assoc` of "output_config" drops whichever key arrived first.
  (let [output-config (cond-> {}
                        effort (assoc "effort" effort)
                        fmt    (assoc "format" {"type" "json_schema" "schema" fmt}))]
    (cond-> {"model" (or model default-model)
             "max_tokens" (or max-tokens (if stream? 64000 16000))
             "messages" (mapv encode-message messages)}
      (seq system)        (assoc "system" (encode-system system))
      (seq tools)         (assoc "tools" (vec tools))
      (seq output-config) (assoc "output_config" output-config)
      thinking-display    (assoc "thinking" {"type" "adaptive" "display" thinking-display})
      fallbacks           (assoc "fallbacks" fallbacks)
      stream?             (assoc "stream" true))))

;; ---- response decoding --------------------------------------------------

(defn- parse-block [b]
  (let [t (get b "type")]
    (merge {:raw b}
           (case t
             "text"     {:type :text :text (get b "text")}
             "thinking" {:type :thinking :text (get b "thinking")}
             "tool_use" {:type :tool-use :id (get b "id")
                         :name (get b "name") :input (get b "input")}
             {:type :other :block-type t}))))

(defn parse-response
  "The API's JSON message -> the neutral response map (`vaelii.host.llm.protocol`)."
  [m]
  {:stop-reason  (get m "stop_reason")
   :stop-details (get m "stop_details")
   :model        (get m "model")
   :usage        (get m "usage")
   :content      (mapv parse-block (get m "content" []))})

;; ---- transport ----------------------------------------------------------

(defn- headers
  [{:keys [kind value]} extra-betas]
  (let [betas (cond-> (vec extra-betas)
                (= :bearer kind) (conj "oauth-2025-04-20"))]
    (cond-> {"content-type" "application/json"
             "anthropic-version" api-version}
      (= :api-key kind) (assoc "x-api-key" value)
      (= :bearer kind)  (assoc "authorization" (str "Bearer " value))
      (seq betas)       (assoc "anthropic-beta" (str/join "," (distinct betas))))))

(defn- request-builder
  "The request to send, headers and all.

  One of those header values is the credential, and the JDK **quotes a rejected value
  verbatim** in the `IllegalArgumentException` it raises for a CR, LF, control or
  non-ASCII character.  That exception travels: the browser puts an error message on the
  page.  So the throw is replaced here by one that names the header and never the value,
  which is what makes `credentials`' promise a guarantee rather than an intention."
  ^HttpRequest$Builder [conn payload betas]
  (let [^HttpRequest$Builder rb (HttpRequest/newBuilder
                                 (URI/create (str (:base-url conn) "/v1/messages")))]
    (.timeout rb (Duration/ofMillis (long (:timeout-ms conn))))
    (doseq [[k v] (headers (:credential conn) betas)]
      (try
        (.header rb ^String k ^String v)
        (catch Exception _
          (throw (ex-info (str "the " k " header holds a character an HTTP header cannot "
                               "carry — a credential read from the environment with a "
                               "trailing newline or a control character in it is the "
                               "usual cause")
                          {:type :llm-bad-credential :header k})))))
    (.POST rb (HttpRequest$BodyPublishers/ofString ^String (json/generate-string payload)))
    rb))

(defn- decode
  "This API's JSON-body refusal — `http/decode` with the endpoint supplied, so the read
  sites below stay a one-argument call."
  [text status]
  (http/decode endpoint text status))

(defn- api-error
  "The exception for a failed call — the API's own `error.message` where there is one,
  else the body.

  **The message is bounded, the body is data** — `http/decode`'s rule, and for the same
  reason: the failing body is whatever answered, a proxy in front of the API answers
  megabytes of HTML, and a megabyte in a message is a megabyte in every log line that
  reports it.  `http/excerpt` bounds what the message carries; the whole text rides under
  `:body`, where a caller that wants it reads it deliberately."
  [status ^String body-text]
  (let [parsed (try (json/parse-string body-text) (catch Exception _ nil))]
    (ex-info (str "Anthropic API " status ": "
                  (http/excerpt (str (or (get-in parsed ["error" "message"]) body-text))))
             {:type :llm-api-error
              :status status
              :error-type (get-in parsed ["error" "type"])
              :body body-text})))

(defn- betas-for [request]
  (when (:fallbacks request "default") [fallback-beta]))

(defn- do-complete [conn request]
  (let [^HttpClient http (:http conn)
        payload (body request {:stream? false})
        ^HttpResponse resp (.send http (.build (request-builder conn payload (betas-for request)))
                                  (HttpResponse$BodyHandlers/ofString))
        status (.statusCode resp)
        text   ^String (.body resp)]
    (if (<= 200 status 299)
      (parse-response (decode text status))
      (throw (api-error status text)))))

;; ---- SSE ----------------------------------------------------------------

(defn- apply-event
  "Fold one decoded SSE event into the accumulating response, and forward the caller's
  view of it.  Returns the next accumulator."
  [acc ev on-event]
  (case (get ev "type")
    "message_start"
    (let [m (get ev "message")]
      (assoc acc :model (get m "model") :usage (get m "usage")))

    "content_block_start"
    (let [i (get ev "index")
          b (get ev "content_block")]
      (on-event {:type :block-start :block (parse-block b)})
      (assoc-in acc [:blocks i] {:raw b :buf (StringBuilder.)}))

    "content_block_delta"
    (let [i (get ev "index")
          d (get ev "delta")
          ^StringBuilder sb (get-in acc [:blocks i :buf])]
      (case (get d "type")
        "text_delta"       (do (when sb (.append sb ^String (get d "text")))
                               (on-event {:type :text-delta :text (get d "text")})
                               acc)
        "thinking_delta"   (do (when sb (.append sb ^String (get d "thinking"))) acc)
        "input_json_delta" (do (when sb (.append sb ^String (get d "partial_json"))) acc)
        ;; The signature arrives as its own delta, not on the block that opened.  It
        ;; must ride back out on the reassembled block: a thinking block echoed to the
        ;; next turn with a missing or edited signature is rejected.
        "signature_delta"  (assoc-in acc [:blocks i :sig] (get d "signature"))
        acc))

    "content_block_stop"
    (do (on-event {:type :block-stop :index (get ev "index")}) acc)

    "message_delta"
    (-> acc
        (assoc :stop-reason (get-in ev ["delta" "stop_reason"])
               :stop-details (get-in ev ["delta" "stop_details"]))
        (update :usage merge (get ev "usage")))

    "error"
    (throw (ex-info (str "Anthropic stream error"
                         (when-let [t (get-in ev ["error" "type"])] (str " (" t ")"))
                         ": " (http/excerpt (str (or (get-in ev ["error" "message"])
                                                     (pr-str ev)))))
                    {:type :llm-api-error :error-type (get-in ev ["error" "type"])}))

    acc))

(defn- finish-block
  "Close one accumulated streamed block back into its JSON shape, then parse it.  The
  reassembled JSON is what `:raw` carries, so the block echoes back byte-for-byte what
  a non-streamed turn would have returned."
  [{:keys [raw sig ^StringBuilder buf]}]
  (let [s (str buf)]
    (parse-block
     (case (get raw "type")
       "text"     (assoc raw "text" s)
       "thinking" (cond-> (assoc raw "thinking" s) sig (assoc "signature" sig))
       "tool_use" (assoc raw "input" (if (str/blank? s) {} (json/parse-string s)))
       raw))))

(defn- collect
  "Fold a sequence of decoded SSE events into the response map they describe — the same
  shape `parse-response` produces for a non-streamed turn."
  [events on-event]
  (let [acc (reduce (fn [acc ev] (apply-event acc ev on-event))
                    {:blocks (sorted-map)}
                    events)]
    {:stop-reason  (:stop-reason acc)
     :stop-details (:stop-details acc)
     :model        (:model acc)
     :usage        (:usage acc)
     :content      (mapv finish-block (vals (:blocks acc)))}))

(defn- do-stream [conn request on-event]
  (let [^HttpClient http (:http conn)
        payload (body request {:stream? true})
        ;; taken before the send, so `:timeout-ms` bounds the whole turn rather than the
        ;; headers and then the body for that long again
        deadline (+ (System/currentTimeMillis) (long (:timeout-ms conn)))
        ^HttpResponse resp (.send http (.build (request-builder conn payload (betas-for request)))
                                  (HttpResponse$BodyHandlers/ofInputStream))
        status (.statusCode resp)
        ^InputStream in (.body resp)]
    (http/under-read-deadline
     endpoint
     (max 1 (- deadline (System/currentTimeMillis)))
     #(.close ^InputStream in)
     (fn []
       (with-open [rdr (BufferedReader. (InputStreamReader. in StandardCharsets/UTF_8))]
         (let [lines (line-seq rdr)]
           (when-not (<= 200 status 299)
             (throw (api-error status (str/join "\n" lines))))
           (let [events (->> lines
                             (filter #(str/starts-with? ^String % "data: "))
                             (map #(decode (subs ^String % 6) status)))
                 response (collect events on-event)]
             (on-event {:type :done :response response})
             response)))))))

;; ---- the provider -------------------------------------------------------

(defn provider
  "An Anthropic-backed `Provider`.

  `opts`:

    :credential  `{:kind :api-key|:bearer :value \"…\"}` — resolved from the
                 environment by `credentials` when absent
    :base-url    default `https://api.anthropic.com` (or `ANTHROPIC_BASE_URL`)
    :timeout-ms  default 600000 — a high-effort turn on a hard task runs for minutes.
                 Bounds the whole turn, the streamed body included, so a host that goes
                 quiet mid-answer releases the thread rather than holding it

  Throws when no credential is reachable, so a caller that may run without one should
  gate on `available?` and fall back to `vaelii.host.llm.stub/provider`."
  ([] (provider {}))
  ([{:keys [credential base-url timeout-ms]
     :or {timeout-ms 600000}}]
   (let [credential (or credential (credentials))
         _ (when-not credential
             (throw (ex-info (str "no Anthropic credential: set ANTHROPIC_API_KEY, or "
                                  "ANTHROPIC_AUTH_TOKEN, or run `ant auth login`")
                             {:type :llm-no-credential})))
         ^HttpClient$Builder b (HttpClient/newBuilder)
         ;; `http/connect-timeout-ms`, not the turn's budget: `timeout-ms` bounds the
         ;; *answer*, and an API that never completes a handshake would otherwise hold the
         ;; calling thread for the ten minutes a hard turn is allowed.
         _ (.connectTimeout b (Duration/ofMillis (long http/connect-timeout-ms)))
         conn {:base-url (or base-url (System/getenv "ANTHROPIC_BASE_URL") "https://api.anthropic.com")
               :timeout-ms timeout-ms
               :credential credential
               :http (.build b)}]
     (reify proto/Provider
       (complete [_ request] (do-complete conn request))
       (stream [_ request on-event] (do-stream conn request on-event))))))
