;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.llm.session
  "The turn loop: propose → validate → repair → an edit batch.

  **The model never writes.**  Its output is `{:add [[sentence context opts?] …]
  :remove [handle …]}` — the exact shape `vaelii.core/edit!` takes, and the exact shape
  the browser's textarea editor already produces.  So a proposal lands in the existing
  editor as a reviewable diff: no new write path, no new trust boundary, and no way
  for a model turn to reach storage.  Applying is a separate, explicit call
  (`apply-proposal!`), which is where the `!` lives.

  **The well-formedness checker is the critic.**  `check-batch` is
  `vaelii.core/check-edit` — `assert`'s own check chain run over each proposed entry
  for its answer rather than its effect, storing nothing, reporting each failure with
  the same `:type` keyword `assert` would have thrown (`:naming`, `:not-ground`,
  `:not-range-restricted`, `:not-well-formed`, `:not-stratified`, `:arg-type`,
  `:disjoint`, `:functional`).  That is a deterministic grader rather than a
  model-judged one, which is what makes the repair loop terminate on a fact rather
  than on an opinion — and sharing the writer's own chain is what keeps the two from
  drifting, so the model is never graded more leniently than it will be applied.

  **The loop is bounded twice.**  `:max-repairs` caps how many times a rejected batch
  is fed back, and `:max-turns` caps total provider turns including tool calls, so
  neither a stubborn model nor a tool-calling one can spin.  Running out of repairs is
  a reported outcome (`:status :invalid` with the rejections), not an exception.

  **Two `:stop-reason`s are read before the content, not one.**  A refusal
  (`proto/refused?`) is the well-known one; the other is `max_tokens` (`truncated?`),
  where the host cut the turn and what arrived is a *prefix* of the answer.  A prefix
  parses, so nothing downstream can tell it from a whole answer — and where the answer is
  **diffed against what was sent** (`propose-edit`), absence is read as intent, so the
  rows the model never reached would come back as proposed retractions.  Hence
  `:status :truncated` on the two paths that diff or carry a `:remove`, and an
  `:answer-truncated?` flag on the two additive ones, where a short answer costs
  assertions and proposes nothing."
  (:require [cheshire.core :as json]
            [clojure.edn :as edn]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.host.llm.correct :as correct]
            [vaelii.host.llm.inventory :as inventory]
            [vaelii.host.llm.page :as page]
            [vaelii.host.llm.prompt :as prompt]
            [vaelii.host.llm.protocol :as proto]
            [vaelii.host.llm.selection :as selection]
            [vaelii.host.llm.stub :as stub]
            [vaelii.host.llm.text :as text]
            [vaelii.host.llm.tools :as tools]
            [vaelii.impl.sentex :as sx]))

;; ---- parsing the proposal ----------------------------------------------
;; Every read of model text in this namespace catches **`Throwable`**, not `Exception`.
;; A deeply nested form overflows the reader's stack with a `StackOverflowError`, which
;; an `Exception` catch lets past — and it then escapes the turn loop entirely, where an
;; answer that cannot be read is the *ordinary* outcome these arms exist to report as a
;; status.  The model's output is untrusted input on every path here, so the depth of a
;; form is not something the parser gets to assume.  `vaelii.browser.web` reads its textarea
;; the same way and says so at the site.

(def ^:private fence
  #"(?s)```(?:edn|clojure|clj)?\s*\n(.*?)```")

(defn parse-batch
  "Pull the proposed batch out of a model's answer.

  Reads the **last** fenced block (a model often shows a wrong draft before the final
  one), falling back to the whole text when there is no fence, with
  `clojure.edn/read-string` — never `read-string`, so a model's output cannot evaluate
  code.  Returns `{:batch {:add […] :remove […]}}` or `{:error \"…\"}`."
  [text]
  (let [blocks (map second (re-seq fence (or text "")))
        src    (or (last blocks) text)]
    (if (str/blank? src)
      {:error "no edit batch found: answer with one fenced `edn` block holding {:add [...] :remove [...]}"}
      ;; the class name when there is no message, because a `StackOverflowError` carries
      ;; none and the marker has to be truthy — a nil there would read as a map with
      ;; neither key, which is an *empty batch*
      (let [form (try (edn/read-string src)
                      (catch Throwable e {::unreadable (or (ex-message e)
                                                           (.getName (class e)))}))]
        (cond
          (::unreadable form) {:error (str "the edn block does not parse: " (::unreadable form))}
          (not (map? form))   {:error (str "the edn block must be a map with :add and/or :remove, got "
                                           (pr-str (type form)))}
          :else
          (let [add (:add form) rm (:remove form)]
            (cond
              (and (some? add) (not (sequential? add)))
              {:error ":add must be a vector of [sentence context] entries"}
              (and (some? rm) (not (sequential? rm)))
              {:error ":remove must be a vector of integer handles"}
              :else {:batch {:add (vec add) :remove (vec rm)}})))))))

;; ---- the deterministic critic ------------------------------------------
;; The critic is `vaelii.core/check-edit` — `assert`'s own chain run for its answer
;; rather than its effect, storing nothing.  Going through the public read keeps the
;; grader and the writer definitionally identical: a check `assert` gains is a check
;; the model is held to on the next call, with no second copy to drift.  It also means
;; the loop grades rules as strictly as facts — range restriction, the imperative ban,
;; and rule-set stratification are all reachable only through that chain.

(defn placement-problem
  "The problem with an entry whose sentence would file itself **somewhere other than the
  context the entry names**, or nil.

  `(ist Ctx S)` is find-or-create in `Ctx`, so an entry
  `[(ist CxCriedWolf (dog Sneaky)) CxLionMouse]` stores in `CxCriedWolf`
  and the context column a reviewer reads is a lie.  Nothing in the check chain objects —
  the sentence is well-formed and every name in it is legal — so this is checked here,
  where the entry and its intended context are both in hand.

  It matters most on the two paths that promise the context is **the caller's** and not
  the model's (`propose-page`, `propose-text`), where it is the only way that promise can
  be broken; it is refused on the other two as well, because a line whose displayed
  context contradicts where it lands is a bad line to show a reviewer whoever wrote it.

  Only a **top-level** `ist`.  The check chain refuses an `ist` in any rule position as
  `:not-well-formed` (docs/contexts.md), so this check does not repeat that refusal."
  [entry]
  (let [[sentence context] (when (sequential? entry) entry)]
    ;; `sequential?`, not `seq?`: the line is model-written EDN, and a bracketed
    ;; `[ist …]` is refused by `assert`'s shape guard anyway — but it is refused *here*,
    ;; with the message that names the placement rather than the brackets, since what
    ;; the writer has to be told either way is to write the bare sentence and let the
    ;; context be the caller's.  A bracket is not the escape hatch from the one check
    ;; that keeps it so.
    (when (and (sequential? sentence) (seq sentence) (= sx/ist-functor (first sentence)))
      {:type :context-escape
       :message (str "the sentence is an `ist`, so it would be filed in "
                     (pr-str (second sentence)) " rather than in " (pr-str context)
                     " — write the bare sentence and let the context be the caller's")})))

(defn check-batch
  "Every problem in a batch, as
  `[{:in :add|:remove :index i :entry e :type k :message \"…\"} …]` — empty when the
  batch is admissible.  Adds are checked against the KB as it stands; a removal is
  checked only for naming an actually stored handle.

  The `:type` is the one `assert` would have thrown, so a rejection fed back to the
  model names the same failure the apply would have hit — plus `:context-escape`, the one
  problem the chain cannot see (`placement-problem`), since `assert` would carry that
  entry out *correctly* and into the wrong context."
  [kb batch]
  (into (vec (keep-indexed (fn [i entry]
                             (some-> (placement-problem entry)
                                     (assoc :in :add :index i :entry entry)))
                           (:add batch)))
        (v/check-edit kb batch)))

(defn check-entry
  "The first problem in one `[sentence context opts?]` entry as `{:type … :message …}`,
  or nil when it is admissible — `check-batch` narrowed to a single add, plus
  `placement-problem`, which the chain has no way to see."
  [kb entry]
  (or (placement-problem entry)
      (some-> (first (v/check-edit kb {:add [entry] :remove []}))
              (select-keys [:type :message]))))

;; ---- the second axis: what vocabulary the proposal invents ---------------
;; The critic answers *is this admissible*.  It cannot answer *is this vocabulary the KB
;; can reason with*, because a coined unary predicate is a well-formed type name and
;; always will be.  So every proposal carries a second, orthogonal report beside its
;; rejections — see `vaelii.host.llm.inventory`, where the check and its prevention live.

(defn coined
  "The vocabulary a proposed batch introduces:
  `{:coined [{:predicate :arity :role :in :index} …] :vocabulary {…}}`.

  Reported, never rejected — coining a type is how an ontology grows, and which side of
  that a given proposal falls on is a human's call.  Called through here for the same
  reason `check-batch` is: one place a caller looks for what a proposal was graded on."
  [kb batch]
  (inventory/coined kb batch))

;; ---- feeding the critic back -------------------------------------------

(defn- rejection-line [{:keys [in index entry type message]}]
  (str "- " (name in) "[" index "] " (pr-str entry) "\n  " type " — " message))

(defn repair-prompt
  "The turn handed back to the model after a rejected batch: the typed rejections,
  verbatim, and nothing else to argue with."
  [rejections]
  (str "The batch was rejected by the knowledge base's own well-formedness checks. "
       "Each line gives the entry, the rejection type, and the checker's message:\n\n"
       (str/join "\n" (map rejection-line rejections))
       "\n\nFix every one of them and answer with a corrected batch in a single fenced "
       "`edn` block. Use the read tools to check anything you are unsure of — a type's "
       "supertypes, a predicate's arg constraints, an individual's existing types. "
       "Drop an entry you cannot make well-formed rather than guessing at it."))

;; ---- the loop -----------------------------------------------------------

(defn truncated?
  "Did the host stop this turn at the **token limit**?

  `proto/refused?`'s sibling, and the other `:stop-reason` that has to be read before
  anything reads the content.  A turn cut at `max_tokens` carries a *prefix* of the
  answer, and a prefix of a well-formed answer is often itself well-formed — so nothing
  downstream can tell it from a complete one.

  On the selection path that is not a cosmetic loss.  `diff-batch` reads the lines that
  came back as the whole of what the model kept, so **every selected row the stream never
  reached becomes a proposed retraction**: a transport artifact rendered to a reviewer as
  a deliberate deletion.  Hence a status of its own, decided before the diff runs.

  Repairing is not the answer either, and none of the loops feeds one back: the model did
  not get the answer wrong, it ran out of room, so the same turn re-asked returns the same
  prefix until `:max-tokens` moves."
  [response]
  (= "max_tokens" (:stop-reason response)))

(defn- run-turn
  [provider request on-event]
  (if on-event
    (proto/stream provider request on-event)
    (proto/complete provider request)))

(defn- tool-results
  "Run each tool-use block and return the user turn carrying the results.  All results
  of one assistant turn go back in a single message."
  [kb response opts]
  {:role "user"
   :content (mapv (fn [{:keys [id name input]}]
                    (let [{:keys [ok result error]} (tools/call kb name input opts)]
                      {:type :tool-result
                       :tool-use-id id
                       :content (if ok result (str "error: " error))
                       :error? (not ok)}))
                  (proto/tool-uses response))})

(defn propose
  "Ask `provider` for an edit batch and return a **proposal** — never applied.

  This is the entry point an application (the browser's panel, the CLI) calls.
  `opts`:

    :message      the user's request (required)
    :provider     a `vaelii.host.llm.protocol/Provider` (default: the offline stub)
    :system       override the generated system prompt (default: generated from `kb`)
    :prompt-opts  passed to `vaelii.host.llm.prompt/system-prompt`
    :tool-opts    passed to `vaelii.host.llm.tools/schemas` (`:only` / `:exclude`)
    :model :max-tokens :effort :thinking-display   forwarded to the provider
    :max-repairs  rejected batches fed back before giving up (default 2)
    :max-turns    total provider turns, tool calls included (default 24)
    :on-event     when present, the provider streams and every event is handed here —
                  what an SSE endpoint consumes

  Returns:

    {:status     :ok | :invalid | :unparseable | :refused | :truncated | :exhausted
     :batch      {:add […] :remove […]}   ; present on :ok and :invalid
     :edn        \"…\"                    ; the batch pretty-printed, for the editor
     :rejections [{:in :index :entry :type :message} …]
     :coined     [{:predicate :arity :role :in :index} …]  ; vocabulary it invented
     :vocabulary {:literals :reused :coined :coined-types :coined-relations}
     :text       the model's final prose
     :stop-reason why the host stopped the turn      ; on :truncated
     :attempts   how many batches it proposed
     :turns      how many provider turns it took
     :tool-calls how many read tools it ran
     :messages   the full conversation, for a follow-up turn}

  `:ok` means every entry passed the same checks `assert` runs — not that a human
  agreed with it.  `:refused` means the provider's safety classifiers declined and the
  content is empty or partial; `:truncated` means the host stopped at the token limit,
  so what arrived is a prefix and is reported rather than parsed (`truncated?`);
  `:exhausted` means the turn cap was reached with no final answer."
  [kb {:keys [message provider system prompt-opts tool-opts model max-tokens effort
              thinking-display max-repairs max-turns on-event]
       :or {max-repairs 2 max-turns 24}}]
  (let [provider (or provider (stub/provider))
        system   (or system (prompt/system-prompt kb (or prompt-opts {})))
        schemas  (tools/schemas (or tool-opts {}))
        base     (cond-> {:system [{:text system :cache? true}]
                          :tools schemas}
                   model            (assoc :model model)
                   max-tokens       (assoc :max-tokens max-tokens)
                   effort           (assoc :effort effort)
                   thinking-display (assoc :thinking-display thinking-display))]
    (loop [messages  [{:role "user" :content message}]
           turns     0
           attempts  0
           tool-runs 0]
      (if (>= turns max-turns)
        {:status :exhausted :messages messages :turns turns
         :attempts attempts :tool-calls tool-runs
         :text (str "gave up after " max-turns " turns")}
        (let [response (run-turn provider (assoc base :messages messages) on-event)
              turns    (inc turns)
              messages (conj messages {:role "assistant" :content (:content response)})]
          (cond
            ;; A refusal is a successful HTTP call with empty or partial content, so
            ;; it is checked before anything reads the content.
            (proto/refused? response)
            {:status :refused :stop-details (:stop-details response)
             :messages messages :turns turns :attempts attempts :tool-calls tool-runs
             :text (proto/text response)}

            ;; And truncation for the same reason: the batch in a cut-off answer is a
            ;; prefix of one, so it is reported rather than read.  Ahead of the tool-use
            ;; arm too — a tool call cut in half is an argument map the model never
            ;; finished writing, and running it is worse than not answering.
            (truncated? response)
            {:status :truncated :stop-reason (:stop-reason response)
             :messages messages :turns turns :attempts attempts :tool-calls tool-runs
             :text (proto/text response)}

            (seq (proto/tool-uses response))
            (recur (conj messages (tool-results kb response (or tool-opts {})))
                   turns attempts (+ tool-runs (count (proto/tool-uses response))))

            :else
            (let [text (proto/text response)
                  {:keys [batch error]} (parse-batch text)
                  attempts (inc attempts)
                  repairs-left (- max-repairs (dec attempts))]
              (cond
                error
                (if (pos? repairs-left)
                  (recur (conj messages {:role "user" :content error}) turns attempts tool-runs)
                  {:status :unparseable :text text :messages messages :turns turns
                   :attempts attempts :tool-calls tool-runs
                   :rejections [{:in :batch :index 0 :entry nil :type :unparseable
                                 :message error}]})

                :else
                (let [rejections (check-batch kb batch)
                      out (merge {:batch batch :edn (pr-str batch) :text text
                                  :messages messages :turns turns :attempts attempts
                                  :tool-calls tool-runs}
                                 (coined kb batch))]
                  (cond
                    (empty? rejections)
                    (assoc out :status :ok :rejections [])

                    (pos? repairs-left)
                    (recur (conj messages {:role "user" :content (repair-prompt rejections)})
                           turns attempts tool-runs)

                    :else
                    (assoc out :status :invalid :rejections rejections)))))))))))

;; ---- the selection-scoped loop -----------------------------------------
;; The same critic and the same bounds, over a *selection* rather than the whole KB.
;; What changes is the prompt (`vaelii.host.llm.selection`) and the answer shape: no
;; tools, no fenced block, and decoding constrained to a JSON schema — which is what a
;; completion-only local model can actually do, and what keeps the fixed cost O(the
;; reader's selection) instead of O(the knowledge base).

(def ^:private fenced-block
  #"(?s)```(?:json|edn|clojure|clj|text)?\s*\n?(.*?)```")

(defn- unfence
  "The contents of a markdown fence, when the answer is wrapped in one.  Models fence
  unprompted — one of them does it *while* decoding under a JSON schema that has no way
  to express a fence — so the wrapper is stripped rather than argued with."
  [text]
  (or (second (re-find fenced-block (str text))) (str text)))

(defn- entry-of
  "A read `[sentence context opts?]` -> `{:key [sentence context] :entry […]}`, or
  `{:error …}`.  `:key` drops `opts`, so a line whose only change is its strength is
  still recognised as the same content."
  [v where]
  (cond
    (not (and (vector? v) (<= 2 (count v) 3)))
    {:error (str where " is not [sentence context] or [sentence context opts]: " (pr-str v))}

    (not (sequential? (first v)))
    {:error (str where " has no s-expression in it: " (pr-str v))}

    (not (symbol? (second v)))
    {:error (str where " has no context symbol: " (pr-str v))}

    :else
    {:key [(first v) (second v)] :entry (vec v)}))

(defn- parse-json-lines
  "A JSON envelope `{\"lines\": [{\"sentence\", \"context\", \"strength\"?} …]}` -> the
  same rows the line format yields, or nil when the text is not that shape.  Tolerated
  because a model decoding under `output-schema` answers this way — the contract is the
  line format, but an answer that arrives in the other shape is still an answer."
  [text]
  (let [parsed (try (json/parse-string text) (catch Throwable _ nil))]
    (when (and (map? parsed) (sequential? (get parsed "lines")))
      (let [read (map-indexed
                  (fn [i line]
                    (if-not (map? line)
                      {:error (str "line " (inc i) " is not an object")}
                      (let [s (str (get line "sentence"))
                            c (str (get line "context"))
                            v (try [(edn/read-string s) (edn/read-string c)]
                                   (catch Throwable _ nil))]
                        (if (nil? v)
                          {:error (str "line " (inc i) " does not parse: " (pr-str line))}
                          (entry-of (cond-> v
                                      (= "monotonic" (get line "strength"))
                                      (conj {:strength :monotonic}))
                                    (str "line " (inc i)))))))
                  (get parsed "lines"))
            errs (keep :error read)]
        (if (seq errs)
          {:errors (vec errs)}
          {:rows (vec read) :notes (get parsed "notes")})))))

(defn- parse-editor-lines
  "The contract: one `[sentence context]` (or `[sentence context opts]`) per line, read
  with `clojure.edn/read-string` — never `read-string`, so model output cannot evaluate
  code.  Exactly what the browser's editor already parses, which makes the round trip
  through the textarea the identity.

  A line that is blank, or is prose the model wrote despite being told not to, is not an
  entry — it comes back as `:notes`, which is the only commentary channel this format
  has.  A line that **starts like an entry and is not one** is an error rather than a
  silent drop, because dropping a line is a retraction.  No entries at all is an error
  too, whatever prose came with it."
  [text]
  (let [all   (->> (str/split-lines text) (map str/trim) (remove str/blank?))
        entry-line? #(str/starts-with? % "[")
        lines (filter entry-line? all)
        notes (not-empty (str/join " " (remove entry-line? all)))
        read (map-indexed
              (fn [i line]
                (let [v (try (edn/read-string line) (catch Throwable _ ::unreadable))]
                  (if (= ::unreadable v)
                    {:error (str "line " (inc i) " does not parse: " line)}
                    (entry-of v (str "line " (inc i))))))
              lines)
        errs (keep :error read)]
    (cond
      (empty? lines)
      {:errors [(str "no lines found — answer with one [sentence context] per line, "
                     "each starting with [ and ending with ]")]}
      (seq errs) {:errors (vec errs)}
      :else      {:rows (vec read) :notes notes})))

(defn parse-lines
  "A model's answer -> `{:rows [{:key [sentence context] :entry […]} …] :notes \"…\"}`,
  or `{:errors [\"…\" …]}`.

  Parsed **defensively**, because the answer shape is not something every model can be
  held to: a markdown fence is stripped (models add one unprompted, including while
  decoding under a JSON schema), a JSON envelope is read if one arrives, and otherwise
  — the normal case, and the contract — the text is read as the editor's own lines."
  [text]
  (let [body (unfence text)]
    (or (parse-json-lines body)
        (parse-editor-lines body))))

(defn diff-batch
  "The selection and the model's edited lines -> the `{:add … :remove …}` batch.

  Diffed **by content**, exactly as the browser's editor diffs a saved textarea: a line
  returned unchanged is in both sets and touches nothing, a line rewritten retracts the
  old handle and asserts the new content, a line dropped retracts, a line invented
  asserts.  So no handle churns for knowledge the model left alone."
  [rows proposed]
  (let [orig-keys (set (map :key rows))
        new-keys  (set (map :key proposed))]
    {:add    (mapv :entry (remove #(orig-keys (:key %)) proposed))
     :remove (mapv :handle (remove #(new-keys (:key %)) rows))}))

(defn edit-summary
  "What the model did to the selection, in counts:
  `{:selected :returned :unchanged :removed :added}`.

  Worth reporting separately from the batch because **a dropped line is a retraction**
  — the model deleting a line it was asked to leave alone is legal, well-formed, and
  invisible to the critic, so the one thing a reviewer must not miss is how many
  sentexes the proposal removes.  A content diff cannot tell a rewrite from a
  delete-plus-add, so these are counts of what the diff *is*, not a guess at intent."
  [rows proposed {:keys [add remove]}]
  {:selected  (count rows)
   :returned  (count proposed)
   :unchanged (- (count rows) (count remove))
   :removed   (count remove)
   :added     (count add)})

(defn repair-lines-prompt
  "The turn handed back after a rejected or unreadable answer on the selection path:
  the problems verbatim, and the same instruction as the first turn — return the whole
  edited line set, not a patch."
  [problems]
  (str "That answer was rejected:\n\n"
       (str/join "\n" (map #(str "- " %) problems))
       "\n\nAnswer again with the complete edited set of lines, fixing every problem. "
       "Drop a line you cannot make well-formed rather than guessing at it."))

(defn- lines-text
  "The batch as the editor's textarea content: one `[sentence context]` per proposed
  line, in the model's order — what a browser panel drops straight into the open
  editor for the reader to review and Save."
  [proposed]
  (str/join "\n" (map (comp pr-str :entry) proposed)))

(defn- message-text
  "The text one message contributes to the window — a string content as itself, a block
  vector as its text blocks.  Used to size a *conversation*, not just the first turn."
  [{:keys [content]}]
  (if (string? content)
    content
    (str/join "\n" (keep :text content))))

(defn propose-edit
  "Ask a model to edit **a selection of sentexes** and return a proposal — never
  applied.  This is what a browser selection panel calls.

  `opts`:

    :handles      the selected sentex handles, in page order (required)
    :message      the reader's instruction (required)
    :provider     a `Provider` (default: the offline stub)
    :num-ctx      the context window to size the request against (default 8192)
    :max-repairs  rejected answers fed back before giving up (default 2)
    :max-turns    total provider turns (default 6)
    :prompt-opts  passed to `vaelii.host.llm.selection/vocabulary-card`
    :format       a JSON schema to constrain decoding with — an **optimization** for a
                  model it demonstrably helps, not the contract, which is the editor's
                  line format.  `selection/output-schema` is the one to pass.
    :model :max-tokens :on-event   forwarded to the provider

  Returns:

    {:status     :ok | :invalid | :unparseable | :refused | :truncated | :exhausted
                 | :too-large | :empty-selection
     :batch      {:add […] :remove […]}   ; present on :ok and :invalid
     :edn        \"…\"                    ; the batch, for `apply-proposal!`
     :lines      \"[…]\\n[…]\"            ; the edited lines, for the editor textarea
     :summary    {:selected :returned :unchanged :removed :added}  ; what it did
     :rejections [{:in :index :entry :type :message} …]
     :coined     [{:predicate :arity :role :in :index} …]  ; vocabulary it invented
     :vocabulary {:literals :reused :coined :coined-types :coined-relations}
     :notes      what the model was unsure of
     :selection  [{:handle :line} …]      ; what it was actually shown
     :stop-reason why the host stopped the turn                  ; on :truncated
     :budget     {:prompt :reserved :total :num-ctx :headroom}   ; estimated tokens
     :usage      {:input-tokens :output-tokens …}                ; measured, by the host
     :elapsed-ms wall clock for the whole loop
     :attempts :turns :messages}

  `:too-large` means the request does not fit the window — reported with the numbers
  and **nothing sent**, because the alternative is the host silently truncating the
  reader's own selection.  It is checked before the first turn *and before every repair
  turn*, since a repair carries the whole conversation back.  `:empty-selection` means
  no handle still names a stored sentex.

  `:truncated` is the same failure on the way back, and this is the path it costs the
  most: the answer is diffed **against the selection**, so a row the host cut off before
  the model reached it is a row the diff proposes to retract.  There is no batch on that
  status — a partial line set is not a proposal, and the one shown to a reviewer would be
  a deletion nobody asked for."
  [kb {:keys [handles message provider num-ctx max-repairs max-turns prompt-opts
              model max-tokens on-event]
       fmt :format
       :or {max-repairs 2 max-turns 6 num-ctx 8192}}]
  (let [started  (System/currentTimeMillis)
        provider (or provider (stub/provider))
        rows     (selection/selected kb handles)
        system   selection/system-prompt
        user     (selection/user-turn kb rows message (or prompt-opts {}))
        bdg      (selection/budget system user (count rows) num-ctx)
        problem  (selection/budget-problem bdg (count rows))
        elapsed  #(- (System/currentTimeMillis) started)
        base     {:selection (mapv #(select-keys % [:handle :line]) rows)
                  :budget bdg}]
    (cond
      (empty? rows)
      (assoc base :status :empty-selection :elapsed-ms (elapsed)
             :text "no selected handle names a stored sentex")

      problem
      (assoc base :status :too-large :elapsed-ms (elapsed) :text problem)

      :else
      (let [request (cond-> {:system [{:text system}]
                             :num-ctx num-ctx}
                      fmt        (assoc :format fmt)
                      model      (assoc :model model)
                      max-tokens (assoc :max-tokens max-tokens))
            convo-budget (fn [messages]
                           (selection/budget system
                                             (str/join "\n" (map message-text messages))
                                             (count rows) num-ctx))]
        (loop [messages [{:role "user" :content user}]
               turns    0
               attempts 0
               usage    nil]
          ;; Sized once and held.  The re-check below reads its headroom and the refusal
          ;; reports the whole budget, and estimating it joins every message in the
          ;; conversation — so a delay, which also keeps an exhausted loop from sizing a
          ;; conversation it is about to abandon.
          (let [convo (delay (convo-budget messages))]
            (cond
              (>= turns max-turns)
              (assoc base :status :exhausted :messages messages :turns turns
                     :attempts attempts :usage usage :elapsed-ms (elapsed)
                     :text (str "gave up after " max-turns " turns"))

              ;; A repair carries the whole conversation back, so the window has to be
              ;; re-checked: the first turn fitting says nothing about the third.
              (neg? (:headroom @convo))
              (assoc base :status :too-large :messages messages :turns turns
                     :attempts attempts :usage usage :elapsed-ms (elapsed)
                     :budget @convo
                     :text (str "the conversation outgrew the model's context window after "
                                turns " turns — select fewer sentexes, or raise :num-ctx"))

              :else
              (let [response (run-turn provider (assoc request :messages messages) on-event)
                    turns    (inc turns)
                    usage    (or (:usage response) usage)
                    messages (conj messages {:role "assistant" :content (:content response)})
                    out      (assoc base :messages messages :turns turns :usage usage)]
                (cond
                  (proto/refused? response)
                  (assoc out :status :refused :attempts attempts :elapsed-ms (elapsed)
                         :stop-details (:stop-details response) :text (proto/text response))

                  ;; Before the diff, which is the whole point: `diff-batch` reads absence
                  ;; as intent, so a cut-off line set would propose retracting every row
                  ;; the model never got to.
                  (truncated? response)
                  (assoc out :status :truncated :attempts attempts :elapsed-ms (elapsed)
                         :stop-reason (:stop-reason response) :text (proto/text response))

                  :else
                  (let [text (proto/text response)
                        {proposed :rows :keys [errors notes]} (parse-lines text)
                        attempts (inc attempts)
                        repairs-left (- max-repairs (dec attempts))
                        out (assoc out :attempts attempts :notes notes :text text)]
                    (cond
                      (seq errors)
                      (if (pos? repairs-left)
                        (recur (conj messages {:role "user" :content (repair-lines-prompt errors)})
                               turns attempts usage)
                        (assoc out :status :unparseable :elapsed-ms (elapsed)
                               :rejections (mapv (fn [e] {:in :lines :index 0 :entry nil
                                                          :type :unparseable :message e})
                                                 errors)))

                      :else
                      (let [batch      (diff-batch rows proposed)
                            rejections (check-batch kb batch)
                            out        (merge (assoc out :batch batch :edn (pr-str batch)
                                                     :lines (lines-text proposed)
                                                     :summary (edit-summary rows proposed batch))
                                              (coined kb batch))]
                        (cond
                          (empty? rejections)
                          (assoc out :status :ok :rejections [] :elapsed-ms (elapsed))

                          (pos? repairs-left)
                          (recur (conj messages
                                       {:role "user"
                                        :content (repair-lines-prompt (map rejection-line rejections))})
                                 turns attempts usage)

                          :else
                          (assoc out :status :invalid :rejections rejections
                                 :elapsed-ms (elapsed)))))))))))))))

;; ---- the page-scoped generation loop ------------------------------------
;; The same critic, the same coining flag, the same bounds — over a *term page* instead
;; of a selection.  Three things differ, each measured (`vaelii.host.llm.page`): the model
;; writes **bare sentences** and the caller supplies the context, decoding is
;; **constrained** by a JSON schema (which rescues generation where it would drop lines on
;; the edit path), and the answer is **additive**, so there is nothing to diff and no
;; retraction to miss.
;;
;; The turn always streams, because generation is the slow direction: each assertion is
;; handed to `:on-event` the moment its closing paren arrives, so a panel fills in as the
;; model writes rather than after it finishes.

(defn unescape
  "A JSON string's escapes undone, in one pass.  The incremental scanner reads
  s-expressions straight out of the raw response text, so a sentence carrying a Clojure
  string arrives with the JSON layer's backslashes still in it.

  `\\uXXXX` is the escape that matters here and the one a single-character pattern cannot
  read: a host that encodes non-ASCII — and several do, for every character above 127 —
  sends `caf\\u00e9`, so dropping the backslash alone leaves `cafu00e9` inside the
  sentence.  The four hex digits are read as a code unit, and a surrogate pair reassembles
  because both halves land in the same output string.  The alternation is ordered so
  `\\\\u0041` stays a backslash followed by a literal `u0041`, not the letter A."
  [s]
  (str/replace (str s) #"\\u([0-9a-fA-F]{4})|\\(.)"
               (fn [[_ hex c]]
                 (if hex
                   (str (char (Integer/parseInt hex 16)))
                   (case c "n" "\n" "t" "\t" "r" "\r" "b" "\b" "f" "\f"
                         "\"" "\"" "\\" "\\" c)))))

(defn read-sentence
  "One s-expression's text -> the sentence, or nil when it is not one.  Read with
  `clojure.edn/read-string` — never `read-string` — so model output cannot evaluate code,
  and retried unescaped for text lifted out of a JSON string."
  [text]
  (let [try-read #(try (let [v (edn/read-string %)] (when (sequential? v) v))
                       (catch Throwable _ nil))]
    (or (try-read (str text)) (try-read (unescape text)))))

(def scan-init
  "The initial state of the incremental s-expression scanner."
  {:depth 0 :esc? false :buf nil})

(defn scan
  "Fold one streamed text delta into the scanner state, returning
  `[state' [\"(…)\" …]]` — every s-expression whose closing paren arrived in this delta.

  Deliberately shape-blind: it counts parentheses and skips backslash escapes, so the
  same scanner reads sentences out of the JSON envelope (where each is a string value) and
  out of a bare-line answer.  A quoted Clojure string holding an *unbalanced* parenthesis
  would confuse it — which costs a progress event and nothing more, since the batch is
  built by parsing the finished text."
  [state delta]
  (let [out (volatile! [])
        st (reduce
            (fn [{:keys [depth esc? buf] :as s} ch]
              (cond
                esc?      (assoc s :esc? false :buf (when buf (str buf ch)))
                (= \\ ch) (assoc s :esc? true :buf (when buf (str buf ch)))
                (= \( ch) (assoc s :depth (inc depth) :buf (str buf ch))
                (zero? depth) s
                (= \) ch) (let [d (dec depth) b (str buf ch)]
                            (if (zero? d)
                              (do (vswap! out conj b) (assoc s :depth 0 :buf nil))
                              (assoc s :depth d :buf b)))
                :else     (assoc s :buf (str buf ch))))
            state
            (str delta))]
    [st @out]))

(defn- json-assertions
  "The constrained-decoding shape — `{\"assertions\": [{\"sentence\", \"strength\"?} …],
  \"notes\": \"…\"}` — or nil when the text is not that shape.  A bare JSON array is read
  too, and so is a plain string element, because a model under a schema still occasionally
  flattens one level."
  [text]
  (let [parsed (try (json/parse-string text) (catch Throwable _ nil))
        items  (cond
                 (and (map? parsed) (sequential? (get parsed "assertions"))) (get parsed "assertions")
                 (sequential? parsed) parsed)]
    (when items
      (let [read (map-indexed
                  (fn [i item]
                    (let [text (str (if (map? item) (get item "sentence") item))]
                      (if-let [form (read-sentence text)]
                        {:sentence form
                         :strength (when (= "monotonic" (and (map? item) (get item "strength")))
                                     :monotonic)}
                        {:problem (str "assertion " (inc i) " is not an s-expression: "
                                       (pr-str item))})))
                  items)]
        {:sentences (vec (filter :sentence read))
         :problems (vec (keep :problem read))
         :notes (when (map? parsed) (get parsed "notes"))}))))

(defn- line-assertions
  "The fallback shape: one bare s-expression per line, which is what a model that ignores
  `format` writes.  A list marker (`- `, `1. `) is stripped, prose becomes `:notes`, and a
  line that starts like a sentence and does not read becomes a problem rather than a
  silent drop."
  [text]
  (let [lines (->> (str/split-lines (str text))
                   (map str/trim)
                   (remove str/blank?)
                   (map #(str/replace % #"^(?:[-*+]|\d+[.)])\s+" "")))
        sexp? #(str/starts-with? % "(")
        read  (map-indexed (fn [i l]
                             (if-let [form (read-sentence l)]
                               {:sentence form}
                               {:problem (str "line " (inc i) " does not parse: " l)}))
                           (filter sexp? lines))]
    {:sentences (vec (filter :sentence read))
     :problems (vec (keep :problem read))
     :notes (not-empty (str/join " " (remove sexp? lines)))}))

(defn parse-assertions
  "A model's answer -> `{:sentences [{:sentence :strength} …] :notes \"…\" :problems […]}`,
  or `{:errors [\"…\" …]}` when nothing readable came back.

  The JSON envelope is the contract here (decoding is constrained to it), with a
  markdown fence stripped first — models fence unprompted, including while decoding under
  a schema that cannot express one — and bare lines read as the fallback.  Unlike the edit
  path, a line the parser cannot read is a **problem, not a failure**: this answer only
  adds, so the readable assertions stand on their own and the unreadable ones are reported
  beside them."
  [text]
  (let [body (unfence text)
        parsed (or (json-assertions body) (line-assertions body))]
    (if (seq (:sentences parsed))
      parsed
      {:errors (or (not-empty (:problems parsed))
                   [(str "no assertions found — answer with a JSON object like "
                         "{\"assertions\": [{\"sentence\": \"(genl penguin aquatic_bird)\"}]}")])})))

(defn- stored?
  "Is this sentence already in `context`?  `handle-of` finds without creating; model output
  is arbitrary, so a sentence too malformed to even look up is simply not stored."
  [kb sentence context]
  (try (some? (v/handle-of kb sentence context))
       (catch Throwable _ false)))

(defn new-assertions
  "The read sentences -> `{:entries [[sentence context opts?] …] :known […] :duplicates […]}`.

  Two kinds of non-news are separated out rather than proposed: a sentence the KB
  **already stores** in this context (re-asserting is a no-op find-or-create, so it is
  noise in a diff), and one the model wrote **twice**.  Both are counted for the reviewer,
  because a proposal that is 80% restatement is a different thing from one that is not.

  `->entry` builds the entry for a kept item and defaults to the page path's, which carries
  nothing but strength.  The reading path passes its own, because a candidate read out of
  text carries a **span** into provenance — and asking *is this already stored* is the same
  question on both paths, so it is asked in one place rather than twice."
  ([kb context items]
   (new-assertions kb context items
                   #(page/assertion-entry (:sentence %) context (:strength %))))
  ([kb context items ->entry]
   (-> (reduce (fn [acc {:keys [sentence] :as item}]
                 (cond
                   (contains? (:seen acc) sentence)
                   (update acc :duplicates conj sentence)

                   (stored? kb sentence context)
                   (-> acc (update :known conj sentence) (update :seen conj sentence))

                   :else
                   (-> acc
                       (update :entries conj (->entry item))
                       (update :seen conj sentence))))
               {:entries [] :known [] :duplicates [] :seen #{}}
               items)
       (dissoc :seen))))

(defn assertion-summary
  "What the model produced, in counts: `{:proposed :new :known :duplicate :monotonic}` —
  how many assertions it wrote, how many are new knowledge, how many restate what is
  already stored, how many it repeated, and how many of the **new** entries the model
  claimed as `:monotonic` known-truth.

  The last is the review hook the reader's own strength grant needs: a `:monotonic`
  candidate strength-defeats a hand-written `:default` it contradicts, so a translated
  guess arriving as known-truth is the sharpest thing this pipeline can produce.  The
  capability is allowed (a reader may legitimately mark a fact known-true), but a count
  of zero every time is what makes a non-zero one worth a second look — a summary that
  never surfaced it left the reviewer with no number to notice.  Counted over `entries`
  alone, since `known` / `duplicate` are bare sentences carrying no strength."
  [sentences {:keys [entries known duplicates]}]
  {:proposed (count sentences)
   :new (count entries)
   :known (count known)
   :duplicate (count duplicates)
   :monotonic (count (filter #(= :monotonic (:strength (nth % 2 nil))) entries))})

(defn repair-assertions-prompt
  "The turn handed back after a rejected or unreadable generation: the problems verbatim,
  and the same contract as the first turn."
  [problems]
  (str "The knowledge base rejected that answer:\n\n"
       (str/join "\n" (map #(str "- " %) problems))
       "\n\nAnswer again, fixing every problem. Keep the assertions that were fine, drop "
       "any you cannot state well-formedly, and write no context."))

(defn- page-turn
  "One page turn on the provider's streaming path.  Each completed s-expression is checked
  and handed to `:on-event` as `{:type :assertion :index :sentence :entry :problem
  :stored?}` the moment it closes, so time-to-first-assertion is the model's first
  sentence rather than its last.  The raw provider events pass through unchanged, so an
  SSE endpoint still sees the deltas."
  [kb provider request {:keys [context on-event started first-ms index]}]
  (let [state (atom scan-init)]
    (proto/stream
     provider request
     (fn [ev]
       (when (= :text-delta (:type ev))
         (let [[st done] (scan @state (:text ev))]
           (reset! state st)
           (doseq [text done]
             (when-let [s (read-sentence text)]
               (let [i (dec (swap! index inc))
                     entry (page/assertion-entry s context nil)]
                 (compare-and-set! first-ms nil (- (System/currentTimeMillis) started))
                 (when on-event
                   (on-event {:type :assertion :index i :sentence s :entry entry
                              :problem (check-entry kb entry)
                              :stored? (stored? kb s context)})))))))
       (when on-event (on-event ev))))))

(defn propose-page
  "Ask a model for **new knowledge about the term on a page** and return a proposal —
  never applied.  This is what a term page's panel calls when the reader types something
  open-ended (\"flesh out the capabilities of this\").

  `opts`:

    :term         the page's term, a symbol (required)
    :message      the reader's instruction (required)
    :context      the context new assertions are filed in.  Defaults to the context most
                  of the term's own sentexes are in, else `CxUniverse`; the choice is
                  reported back as `:context`
    :provider     a `Provider` (default: the offline stub)
    :num-ctx      the context window to size the request against (default 8192)
    :max-assertions  how many assertions to ask for, and the output room reserved for
                  them (default 24)
    :max-repairs  rejected answers fed back before giving up (default 1 — an additive
                  answer's good assertions survive a rejection, and a second round costs
                  a whole generation)
    :max-turns    total provider turns (default 4)
    :prompt-opts  passed to `vaelii.host.llm.page/user-turn` — `:max-lines` for the page's
                  own content, `:max-predicates` / `:max-types` / `:max-tokens` for the
                  vocabulary card
    :format       the JSON schema decoding is constrained to.  Defaults to
                  `vaelii.host.llm.page/output-schema`, which is **the contract on this
                  path**; pass `:format nil` to send none
    :model :max-tokens :on-event   forwarded to the provider

  Returns the same shape `propose-edit` does, so one panel handles both:

    {:status     :ok | :invalid | :unparseable | :refused | :exhausted | :too-large
                 | :no-term
     :batch      {:add [[sentence context opts?] …] :remove []}   ; generation never removes
     :edn        \"…\"                    ; the batch, for `apply-proposal!`
     :lines      \"[…]\\n[…]\"            ; the entries, for the editor textarea
     :summary    {:proposed :new :known :duplicate :monotonic}
     :rejections [{:in :index :entry :type :message} …]
     :coined     [{:predicate :arity :role :in :index} …]
     :vocabulary {:literals :reused :coined :coined-types :coined-relations}
     :problems   [\"…\"]                  ; lines the parser could not read
     :notes      what the model was unsure of
     :term :context                       ; what it wrote about, and where it lands
     :page       [{:handle :line} …]      ; the page content it was shown
     :page-found      how many distinct lines the term has (a floor when the scan was cut)
     :page-truncated? did the scan bound cut, so :page-found is that floor
     :answer-truncated?  did the host stop the turn at the token limit
     :budget     {:prompt :reserved :total :num-ctx :headroom}   ; estimated tokens
     :usage      {:input-tokens :output-tokens …}                ; measured, by the host
     :first-assertion-ms                  ; time to the model's first complete assertion
     :elapsed-ms :attempts :turns :messages}

  `:coined` is the one report that matters most here and the only guard against
  vocabulary fragmentation, since the check chain admits a coined unary predicate by
  design — see `vaelii.host.llm.inventory`.

  **`:page` is a sample whenever `:page-found` exceeds its length**, and the two flags
  beside it are how a caller learns that.  The prompt already says so in its heading
  (`page/stored-heading`), so the model is told; carrying the same fact out as ordinary
  keys is what lets the *reviewer* be told too — a reviewer shown 40 lines and no flag
  reads them as the whole of what is stored, which is the reading the heading exists to
  prevent.  `stored-lines` reports it as metadata, and metadata does not survive the
  `select-keys` that builds `:page`, so it is lifted here rather than carried.

  `:answer-truncated?` is the other half: the generation is additive, so a cut-off turn
  costs assertions the model never wrote rather than proposing a retraction — the batch
  that did arrive stands, and the flag says it is a prefix (`truncated?`)."
  [kb {:keys [term context message provider num-ctx max-repairs max-turns max-assertions
              prompt-opts model max-tokens on-event]
       :or {max-repairs 1 max-turns 4 num-ctx 8192 max-assertions 24}
       :as opts}]
  (let [started  (System/currentTimeMillis)
        elapsed  #(- (System/currentTimeMillis) started)
        provider (or provider (stub/provider))
        fmt      (if (contains? opts :format) (:format opts) page/output-schema)]
    (if-not (symbol? term)
      {:status :no-term :elapsed-ms (elapsed)
       :text (str "a page turn needs a term symbol, got " (pr-str term))}
      (let [popts   (merge {:max-tokens (quot num-ctx 2) :max-assertions max-assertions}
                           prompt-opts)
            rows    (page/stored-lines kb term popts)
            ctx     (page/page-context rows context)
            system  page/system-prompt
            user    (page/user-turn kb term rows ctx message popts)
            bdg     (selection/budget system user max-assertions num-ctx)
            problem (selection/budget-problem bdg max-assertions)
            base    {:term term :context ctx :budget bdg
                     :page (mapv #(select-keys % [:handle :line]) rows)
                     :page-found (:found (meta rows))
                     :page-truncated? (boolean (:truncated? (meta rows)))}
            request (cond-> {:system [{:text system}] :num-ctx num-ctx}
                      fmt        (assoc :format fmt)
                      model      (assoc :model model)
                      max-tokens (assoc :max-tokens max-tokens))
            first-ms (atom nil)
            index    (atom 0)
            convo    (fn [messages]
                       (selection/budget system
                                         (str/join "\n" (map message-text messages))
                                         max-assertions num-ctx))]
        (if problem
          (assoc base :status :too-large :elapsed-ms (elapsed) :text problem)
          (loop [messages [{:role "user" :content user}]
                 turns    0
                 attempts 0
                 usage    nil]
            ;; sized once and held, as on the selection path: the re-check reads its
            ;; headroom and the refusal reports the whole budget
            (let [sized (delay (convo messages))]
              (cond
                (>= turns max-turns)
                (assoc base :status :exhausted :messages messages :turns turns
                       :attempts attempts :usage usage :elapsed-ms (elapsed)
                       :text (str "gave up after " max-turns " turns"))

                (neg? (:headroom @sized))
                (assoc base :status :too-large :messages messages :turns turns
                       :attempts attempts :usage usage :elapsed-ms (elapsed)
                       :budget @sized
                       :text (str "the conversation outgrew the model's context window after "
                                  turns " turns — raise :num-ctx"))

                :else
                (let [response (page-turn kb provider (assoc request :messages messages)
                                          {:context ctx :on-event on-event :started started
                                           :first-ms first-ms :index index})
                      turns    (inc turns)
                      usage    (or (:usage response) usage)
                      messages (conj messages {:role "assistant" :content (:content response)})
                      ;; a flag rather than a status, unlike the two paths that diff: an
                      ;; additive answer cut at the token limit is short, not wrong, so the
                      ;; assertions that did arrive stay applicable and the caller is told
                      ;; they are a prefix
                      out      (assoc base :messages messages :turns turns :usage usage
                                      :first-assertion-ms @first-ms
                                      :answer-truncated? (truncated? response))]
                  (if (proto/refused? response)
                    (assoc out :status :refused :attempts attempts :elapsed-ms (elapsed)
                           :stop-details (:stop-details response) :text (proto/text response))
                    (let [text (proto/text response)
                          {:keys [sentences errors notes problems]} (parse-assertions text)
                          attempts (inc attempts)
                          repairs-left (- max-repairs (dec attempts))
                          out (assoc out :attempts attempts :notes notes :text text
                                     :problems (vec problems))]
                      (cond
                        (seq errors)
                        (if (pos? repairs-left)
                          (recur (conj messages {:role "user"
                                                 :content (repair-assertions-prompt errors)})
                                 turns attempts usage)
                          (assoc out :status :unparseable :elapsed-ms (elapsed)
                                 :rejections (mapv (fn [e] {:in :assertions :index 0 :entry nil
                                                            :type :unparseable :message e})
                                                   errors)))

                        :else
                        (let [split      (new-assertions kb ctx sentences)
                              batch      {:add (:entries split) :remove []}
                              rejections (check-batch kb batch)
                              out        (merge (assoc out :batch batch :edn (pr-str batch)
                                                       :lines (str/join "\n" (map pr-str (:add batch)))
                                                       :summary (assertion-summary sentences split))
                                                (coined kb batch))]
                          (cond
                            (empty? rejections)
                            (assoc out :status :ok :rejections [] :elapsed-ms (elapsed))

                            (pos? repairs-left)
                            (recur (conj messages
                                         {:role "user"
                                          :content (repair-assertions-prompt
                                                    (map rejection-line rejections))})
                                   turns attempts usage)

                            :else
                            (assoc out :status :invalid :rejections rejections
                                   :elapsed-ms (elapsed))))))))))))))))

;; ---- the document-scoped reading loop -----------------------------------
;; The same critic, the same coining flag, the same bounds — over **English text** instead
;; of a KB, a selection or a page.  What is new is on both ends of it.
;;
;; On the way in, the source of the lines is a document rather than an instruction, so the
;; prompt is the document cut into numbered spans plus the vocabulary its own words resolved
;; to (`vaelii.host.llm.text`).
;;
;; On the way out, two things this path needs and the others do not.  A candidate carries
;; the **span** it came from into provenance, so an accepted sentence is auditable back to
;; the characters that produced it.  And a rejected candidate is **not** the whole answer's
;; problem: a document yields many claims, most of them fine, so the final pass splits them
;; — the admissible ones become the batch, and each inadmissible one becomes a *repair*
;; carrying its rejection and, where `vaelii.host.llm.correct` has one, the shape to store
;; instead.  A reviewer is never shown a proposal they cannot apply.

(defn parse-candidates
  "A model's answer -> `{:candidates [{:sentence :segment :confidence :strength} …]
  :untranslated […] :notes \"…\" :problems […]}`, or `{:errors […]}` when nothing readable
  came back.

  The JSON envelope is the contract (decoding is constrained to
  `vaelii.host.llm.text/output-schema`), with a fence stripped first.  Unlike the edit path
  there is no fallback to bare lines: a bare sentence carries no segment number, and a
  candidate with no segment has no span — which is most of what this path is for.  A line
  the parser cannot read is a **problem, not a failure**, as on the page path: this answer
  only adds, so the readable candidates stand on their own."
  [text]
  (let [parsed (try (json/parse-string (unfence text)) (catch Throwable _ nil))
        items  (when (map? parsed) (get parsed "candidates"))]
    (if-not (sequential? items)
      {:errors [(str "no candidates found — answer with a JSON object like "
                     "{\"candidates\": [{\"sentence\": \"(dog Muffet)\", \"segment\": 0}]}")]}
      (let [read (map-indexed
                  (fn [i item]
                    (let [src (str (when (map? item) (get item "sentence")))]
                      (if-let [form (read-sentence src)]
                        {:sentence form
                         :segment (let [s (and (map? item) (get item "segment"))]
                                    (when (int? s) s))
                         :confidence (get {"high" :high "medium" :medium "low" :low}
                                          (and (map? item) (get item "confidence")))
                         :strength (when (= "monotonic" (and (map? item) (get item "strength")))
                                     :monotonic)}
                        {:problem (str "candidate " (inc i) " is not an s-expression: "
                                       (pr-str item))})))
                  items)
            cands (vec (filter :sentence read))]
        (if (empty? cands)
          {:errors (or (not-empty (vec (keep :problem read)))
                       ["the answer carried no candidates"])}
          {:candidates cands
           :untranslated (vec (for [u (get parsed "untranslated") :when (map? u)]
                                {:segment (let [s (get u "segment")] (when (int? s) s))
                                 :reason (some-> (get u "reason") str not-empty)}))
           :notes (get parsed "notes")
           :problems (vec (keep :problem read))})))))

(defn split-admissible
  "Every candidate entry sorted into what a reviewer can apply and what they cannot:
  `{:add […] :repairs [{:entry :problem :correction :index} …]}`.

  This is where a document path stops behaving like the other three.  There, a rejected
  entry makes the whole batch `:invalid` and a reviewer is handed something they cannot
  apply; here a document routinely yields thirty claims of which two are malformed, and
  failing all thirty on account of two would make the pipeline useless.  So the batch that
  comes back is **always applicable**, and each rejected candidate arrives explicitly as a
  repair with the checker's own verdict attached — plus `:correction`, the shape
  `vaelii.host.llm.correct` would store instead, for the commonest failure of all: the right
  claim about a type's instances written as a fact about the type symbol."
  [kb entries]
  (reduce (fn [acc [i entry]]
            (if-let [problem (check-entry kb entry)]
              (let [fix (correct/correction kb (first entry))]
                (update acc :repairs conj
                        (cond-> {:index i :entry entry :problem problem}
                          fix (assoc :correction fix))))
              (update acc :add conj entry)))
          {:add [] :repairs []}
          (map-indexed vector entries)))

(defn repair-candidates-prompt
  "The turn handed back after an unreadable answer: the problems verbatim, and the same
  contract as the first turn."
  [problems]
  (str "That answer could not be read:\n\n"
       (str/join "\n" (map #(str "- " %) problems))
       "\n\nAnswer again in the same JSON shape, with a `segment` number on every "
       "candidate. Drop a candidate you cannot state well-formedly and list its sentence "
       "in `untranslated` instead."))

(defn propose-text
  "Read **English** and answer with candidate sentexes — never applied, and never asserted.

  This is the reading direction, and the whole of it is a proposal: nothing in the engine
  can check that a sentence means what a text said (`vaelii.host.gloss` states the argument
  and docs/reading.md answers it), so what comes back is a review queue with the engine's
  own critic already run over it.

  `opts`:

    :text         the document (required)
    :context      the context candidates are filed in (required) — never the model's to
                  write, exactly as on the page path
    :source       what to record as provenance's `:source` (default: `:text`)
    :instruction  what the reader wants out of the document, if anything
    :provider     a `Provider` (default: the offline stub)
    :num-ctx      the context window to size the request against (default 8192)
    :max-candidates  how many to ask for, and the output room reserved (default 40)
    :max-repairs  unreadable answers fed back before giving up (default 1)
    :max-turns    total provider turns (default 4)
    :prompt-opts  passed to `vaelii.host.llm.text/user-turn` (`:max-relations`,
                  `:max-types`, `:max-tokens`)
    :format       the JSON schema decoding is constrained to.  Defaults to
                  `vaelii.host.llm.text/output-schema`, **the contract here**; `nil` sends none
    :model :max-tokens :on-event   forwarded to the provider

  Returns `propose-edit`'s shape, so the same panel handles it, plus the fields only a
  document has:

    {:status      :ok | :invalid | :unparseable | :refused | :exhausted | :too-large
                  | :no-text
     :batch       {:add [[sentence context {:provenance {…}}] …] :remove []} ; always applicable
     :repairs     [{:index :entry :problem :correction} …] ; refused, with the verdict
     :corrections [{:from :to :alternatives :why …} …]     ; admissible and still wrong-shaped
     :coverage    {:segments :covered :uncovered [{:index :span :text :reason} …]}
     :queue       [{:index :entry :flagged? :confidence :segment} …] ; the order to review in
     :candidates  [{:sentence :segment :confidence :strength} …]     ; every claim as read
     :segments    [{:text :span} …]                  ; what the spans point into
     :resolved    [{:surface :term :segment :span} …] ; words that already named something
     :summary     {:proposed :new :known :duplicate :monotonic :applicable :repairs :corrections}
     :answer-truncated?  did the host stop the turn at the token limit
     :lines :edn :rejections :coined :vocabulary :notes :problems
     :budget :usage :elapsed-ms :attempts :turns :messages}

  `:status :ok` means the batch is applicable and says nothing about whether the reading is
  *right* — that is what `:queue` and a person are for.  `:invalid` means nothing survived
  the critic at all.  Every candidate is `:default` unless it claimed otherwise, because a
  translated guess at `:monotonic` would defeat hand-written defaults.

  `:candidates` is every claim the model made, before the winnowing that drops what the KB
  already stores and what the critic refused — which is what a *score* has to be taken over
  (`vaelii.host.llm.score`), since a reading judged only on what survived would be judged
  against the KB it was read into."
  [kb {:keys [text context source instruction provider num-ctx max-repairs max-turns
              max-candidates prompt-opts model max-tokens on-event]
       :or {max-repairs 1 max-turns 4 num-ctx 8192 max-candidates 40}
       :as opts}]
  (let [started  (System/currentTimeMillis)
        elapsed  #(- (System/currentTimeMillis) started)
        provider (or provider (stub/provider))
        fmt      (if (contains? opts :format) (:format opts) text/output-schema)
        src      (or source :text)]
    (if-not (and (string? text) (not (str/blank? text)) (symbol? context))
      {:status :no-text :elapsed-ms (elapsed)
       :text (str "a reading turn needs a document string and a context symbol, got "
                  (pr-str [(type text) context]))}
      (let [popts    (merge {:max-tokens (quot num-ctx 3)} prompt-opts)
            segs     (text/segments text)
            resolved (text/resolutions kb segs)
            system   text/system-prompt
            user     (text/user-turn kb segs resolved context instruction popts)
            bdg      (selection/budget system user max-candidates num-ctx)
            problem  (selection/budget-problem bdg max-candidates)
            base     {:context context :segments (mapv #(dissoc % :index) segs)
                      :resolved resolved :budget bdg}
            request  (cond-> {:system [{:text system}] :num-ctx num-ctx}
                       fmt        (assoc :format fmt)
                       model      (assoc :model model)
                       max-tokens (assoc :max-tokens max-tokens))
            convo    (fn [messages]
                       (selection/budget system
                                         (str/join "\n" (map message-text messages))
                                         max-candidates num-ctx))]
        (if problem
          (assoc base :status :too-large :elapsed-ms (elapsed) :text problem)
          (loop [messages [{:role "user" :content user}]
                 turns    0
                 attempts 0
                 usage    nil]
            ;; sized once and held, as on the other two paths
            (let [sized (delay (convo messages))]
              (cond
                (>= turns max-turns)
                (assoc base :status :exhausted :messages messages :turns turns
                       :attempts attempts :usage usage :elapsed-ms (elapsed)
                       :text (str "gave up after " max-turns " turns"))

                (neg? (:headroom @sized))
                (assoc base :status :too-large :messages messages :turns turns
                       :attempts attempts :usage usage :elapsed-ms (elapsed)
                       :budget @sized
                       :text (str "the conversation outgrew the model's context window after "
                                  turns " turns — send a shorter document, or raise :num-ctx"))

                :else
                (let [response (run-turn provider (assoc request :messages messages) on-event)
                      turns    (inc turns)
                      usage    (or (:usage response) usage)
                      messages (conj messages {:role "assistant" :content (:content response)})
                      ;; a flag, for the page path's reason: the reading is additive, so a
                      ;; turn cut at the token limit costs candidates rather than proposing
                      ;; a retraction — and the document's uncovered spans then say where
                      out      (assoc base :messages messages :turns turns :usage usage
                                      :answer-truncated? (truncated? response))]
                  (if (proto/refused? response)
                    (assoc out :status :refused :attempts attempts :elapsed-ms (elapsed)
                           :stop-details (:stop-details response) :text (proto/text response))
                    (let [answer (proto/text response)
                          {:keys [candidates errors notes problems untranslated]}
                          (parse-candidates answer)
                          attempts (inc attempts)
                          repairs-left (- max-repairs (dec attempts))
                          out (assoc out :attempts attempts :notes notes :text answer)]
                      (if (seq errors)
                        (if (pos? repairs-left)
                          (recur (conj messages {:role "user"
                                                 :content (repair-candidates-prompt errors)})
                                 turns attempts usage)
                          (assoc out :status :unparseable :elapsed-ms (elapsed)
                                 :problems (vec problems)
                                 :rejections (mapv (fn [e] {:in :candidates :index 0 :entry nil
                                                            :type :unparseable :message e})
                                                   errors)))
                        (let [split (new-assertions kb context candidates
                                                    #(text/candidate-entry % context src segs))
                              {:keys [add repairs]} (split-admissible kb (:entries split))
                              batch   {:add add :remove []}
                              coining (coined kb batch)
                              fixes   (:corrections (correct/corrections kb add))
                              flagged (into #{} (concat (map :index (:coined coining))
                                                        (map :index fixes)))
                              ;; `:invalid` means the critic refused everything it was
                              ;; shown — not that nothing was left to show it.  A document
                              ;; whose every claim the KB already stores read *correctly*
                              ;; and proposes an empty batch, and `apply-proposal!` refuses
                              ;; anything but `:ok`, so calling that invalid would block an
                              ;; apply that would rightly do nothing.
                              all-refused? (and (seq (:entries split)) (empty? add))]
                          (assoc (merge out coining)
                                 :status (if all-refused? :invalid :ok)
                                 :batch batch
                                 :edn (pr-str batch)
                                 :lines (str/join "\n" (map pr-str add))
                                 :candidates (vec candidates)
                                 :repairs repairs
                                 :corrections (vec fixes)
                                 :problems (vec problems)
                                 :coverage (text/coverage segs candidates untranslated)
                                 :queue (text/review-queue add flagged)
                                 :summary (assoc (assertion-summary candidates split)
                                                 :applicable (count add)
                                                 :repairs (count repairs)
                                                 :corrections (count fixes))
                                 :rejections (mapv (fn [{:keys [index entry problem]}]
                                                     (assoc problem :in :candidates
                                                            :index index :entry entry))
                                                   repairs)
                                 :elapsed-ms (elapsed)))))))))))))))

;; ---- the explicit apply step -------------------------------------------

(defn apply-proposal!
  "Apply a proposal's batch through `vaelii.core/edit!` — **the only thing in this
  namespace that writes**, and it is never reached from `propose`.

  Refuses a proposal that is not `:ok` unless `{:force? true}` says otherwise, so a
  batch the critic rejected cannot be applied by accident.  `!` because the batch's
  `:remove` retracts stored knowledge.

  Returns

    {:result    <edit! result>   ; nil when the batch was refused
     :applied   how many of :add the KB stored — the whole batch, or **zero**, since
                `edit!` is all-or-nothing
     :failed-at the index in :add the refusal names, or nil (nil with an :error means
                a `:remove` entry was refused, which `edit!` asks after every add)
     :error     {:type :message :exception}, absent when the whole batch applied
     :violations […] :contradictions […]}

  **The critic cannot rule the refusal out, and this is where that shows.**  It grades
  each add against the KB *as it stands* (`check-edit`), so two adds that are each
  admissible and jointly are not — the second contradicting what the first would store —
  both pass and the batch is `:ok`.  The apply then trips the engine's own check on the
  second entry.

  `edit!` takes the whole batch back at that point (docs/api.md), so
  what this reports is a KB unchanged and the entry to fix: `:applied` is zero and
  `:failed-at` is the index the refusal itself names, read off `:index` rather than
  counted back out of the store.  A refusal is *reported* rather than raised because a
  proposal loop wants the status; a caller that wants the throw back has `:error`'s
  `:exception`.

  `:violations` is narrowed to what *this* edit added to the accumulating ledger (a
  derived conclusion the definitional checks dropped) — empty on a refusal, the rollback
  having restored the ledger."
  ([kb proposal] (apply-proposal! kb proposal {}))
  ([kb {:keys [status batch] :as proposal} {:keys [force?]}]
   (when-not (or force? (= :ok status))
     (throw (ex-info (str "refusing to apply a proposal with status " (pr-str status)
                          " — pass {:force? true} to override")
                     {:type :llm-not-applicable :status status
                      :rejections (:rejections proposal)})))
   (let [before (count (v/violations kb))
         add    (vec (:add batch))
         edit   (try {:result (v/edit! kb {:add add :remove (:remove batch)})}
                     (catch Throwable t {:error t}))
         data   (ex-data (:error edit))]
     (cond-> {:result (:result edit)
              ;; zero on a refusal: the entry point put the batch back, so nothing of it stored
              :applied (if (:error edit) 0 (count add))
              :failed-at nil
              :violations (vec (drop before (v/violations kb)))
              :contradictions (vec (v/contradictions kb))}
       (:error edit)
       (assoc :failed-at (when (= :add (:in data)) (:index data))
              :error {:type (:type data)
                      :message (ex-message (:error edit))
                      :exception (:error edit)})))))
