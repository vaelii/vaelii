;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.llm-selection-test
  "The selection-scoped editing path: `vaelii.impl.llm.selection`,
  `vaelii.impl.llm.ollama`, `vaelii.impl.llm.provider`, and
  `vaelii.impl.llm.session/propose-edit`.

  Two tiers.  Everything above the live section runs **offline against the stub** — no
  host, no model, no socket — because what is under test is the pipeline: the line
  format, the selection-bounded vocabulary card, the context budget, the constrained
  answer's parsing, the content diff, and the invariant that proposing writes nothing.

  The live tier talks to a real Ollama and is **opt-in**: `lein test` skips it with a
  printed reason unless `VAELII_LLM_LIVE=1` says otherwise, so an ordinary run makes no
  model call on any machine.  Opted in, it still skips when the host is unreachable or
  the configured model is absent."
  (:require [cheshire.core :as json]
            [clojure.edn :as edn]
            [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.llm.ollama :as ollama]
            [vaelii.impl.llm.protocol :as proto]
            [vaelii.impl.llm.provider :as provider]
            [vaelii.impl.llm.selection :as sel]
            [vaelii.impl.llm.session :as session]
            [vaelii.impl.llm.stub :as stub]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

;; ---- a small world to select from ---------------------------------------

(defn- world
  "Two facts under fresh temporary terms, plus the sub-predicate and the comment that
  make 'say this more specifically' answerable from the card alone.  Returns the terms
  and the handles a test selects on — call it **once** per test, since every call
  invents new terms."
  [kb]
  (let [dog    (tu/fresh-term :type :dog)
        parent (tu/fresh-term :predicate :parentOf)
        father (tu/fresh-term :predicate :fatherOf)
        tom    (tu/fresh-term :individual :Tom)
        ann    (tu/fresh-term :individual :Ann)
        fido   (tu/fresh-term :individual :Muffet)
        ctx    (tu/fresh-term :context :Story)]
    (v/assert kb (list 'genlContext ctx 'CoreContext) 'UniverseContext)
    (v/assert kb (list 'genl father parent) 'CoreContext)
    (v/assert kb (list 'comment parent
                       (str "(" parent " ?parent ?child) means that ?parent is a parent of ?child."))
              'CoreContext)
    {:dog dog :parentOf parent :fatherOf father :ctx ctx
     :Tom tom :Ann ann :Muffet fido
     :h-parent (v/assert kb (list parent tom ann) ctx)
     :h-dog    (v/assert kb (list dog fido) ctx {:strength :monotonic})}))

;; ---- the editor's line format -------------------------------------------

(tu/deftest-kb a-line-is-the-editors-line
  (let [{:keys [h-parent h-dog parentOf Tom Ann ctx]} (world kb)
        rows (sel/selected kb [h-parent h-dog])]
    (is (= 2 (count rows)))
    (is (= [h-parent h-dog] (map :handle rows)) "handle order is the caller's")
    (is (= (pr-str [(list parentOf Tom Ann) ctx]) (:line (first rows)))
        "a fact renders as [sentence context]")
    (testing "a known-true sentex keeps its strength, so a rewrite cannot downgrade it"
      (is (str/includes? (:line (second rows)) ":strength :monotonic")))))

(tu/deftest-kb a-rule-spells-its-direction-and-defeasibility-back
  (let [p   (tu/fresh-term :predicate :pp)
        q   (tu/fresh-term :predicate :qq)
        ctx (tu/fresh-term :context :Rules)]
    (v/assert kb (list 'genlContext ctx 'CoreContext) 'UniverseContext)
    (let [h (v/assert kb (list 'set/defaultRule
                               (list 'set/forwardRule
                                     (list 'implies (list 'and (list p '?x)) (list q '?x))))
                      ctx)
          line (:line (first (sel/selected kb [h])))]
      (is (str/includes? line "set/defaultRule"))
      (is (str/includes? line "set/forwardRule"))
      (testing "and the line reads back as an entry the critic accepts"
        (is (nil? (session/check-entry kb (edn/read-string line))))))))

(tu/deftest-kb a-handle-with-no-sentex-is-dropped-not-faked
  (let [{:keys [h-dog]} (world kb)]
    (is (= [h-dog] (map :handle (sel/selected kb [999999 h-dog]))))
    (is (empty? (sel/selected kb [999999])))))

;; ---- the vocabulary card is bounded by the selection --------------------

(tu/deftest-kb terms-in-finds-the-selections-terms-and-nothing-else
  (let [{:keys [h-parent parentOf Tom Ann ctx dog]} (world kb)
        ts (sel/terms-in (sel/selected kb [h-parent]))]
    (is (contains? ts parentOf))
    (is (contains? ts Tom))
    (is (contains? ts Ann))
    (is (contains? ts ctx) "the context is part of what the selection is about")
    (is (not (contains? ts dog)) "a term the selection does not mention is not on the card")
    (is (not-any? #(or (number? %) (string? %)) ts))))

(tu/deftest-kb the-card-describes-the-selections-terms
  (let [{:keys [h-parent parentOf fatherOf]} (world kb)
        card (sel/vocabulary-card kb (sel/selected kb [h-parent]))]
    (is (str/includes? card (str parentOf)))
    (testing "sub-predicates are on the card — 'more specific' is unanswerable without them"
      (is (str/includes? card (str fatherOf))))
    (testing "and so is the predicate's own documentation"
      (is (str/includes? card "?parent is a parent of ?child")))))

(tu/deftest-kb the-card-does-not-grow-with-the-knowledge-base
  (let [{:keys [h-parent]} (world kb)
        rows   (sel/selected kb [h-parent])
        before (sel/vocabulary-card kb rows)
        other  (tu/fresh-term :predicate :other)
        noise  (tu/fresh-term :context :Noise)]
    (v/assert kb (list 'genlContext noise 'CoreContext) 'UniverseContext)
    (dotimes [i 100]
      (v/assert kb (list other (symbol (str "Noise" i)) (symbol (str "Thing" i))) noise))
    (is (= before (sel/vocabulary-card kb rows))
        "the card is a function of the selection, not of the KB's size")))

;; ---- the context budget -------------------------------------------------

(tu/deftest-kb the-budget-reserves-room-to-answer
  (let [b (sel/budget "sys" "user" 10 8192)]
    (is (= (+ 256 480) (:reserved b)) "one line back per line in, plus slack")
    (is (= (- 8192 (:prompt b) (:reserved b)) (:headroom b)))
    (is (nil? (sel/budget-problem b 10)))))

(tu/deftest-kb an-oversized-selection-is-refused-with-numbers
  (let [b   (sel/budget (apply str (repeat 40000 "x")) "u" 60 8192)
        msg (sel/budget-problem b 60)]
    (is (neg? (:headroom b)))
    (is (string? msg))
    (is (str/includes? msg "60 sentexes"))
    (is (str/includes? msg "8192"))))

(tu/deftest-kb the-token-estimate-is-conservative
  (testing "estimating high is what makes a refusal safe rather than a silent truncation"
    (is (> (sel/estimate-tokens (apply str (repeat 400 "a"))) (/ 400 4.0)))))

;; ---- the answer, parsed defensively -------------------------------------

(tu/deftest-kb the-contract-is-the-editors-line-format
  (let [{:keys [rows]} (session/parse-lines
                        (str "[(dog Muffet) WellContext]\n"
                             "[(parentOf Tom Ann) WellContext {:strength :monotonic}]"))]
    (is (= 2 (count rows)))
    (is (= ['(dog Muffet) 'WellContext] (:key (first rows))))
    (is (= ['(dog Muffet) 'WellContext] (:entry (first rows))))
    (testing "strength rides across, so a known-true line is not silently downgraded"
      (is (= ['(parentOf Tom Ann) 'WellContext {:strength :monotonic}] (:entry (second rows)))))
    (testing "and it is not part of the key, so re-strengthening is not a rewrite"
      (is (= ['(parentOf Tom Ann) 'WellContext] (:key (second rows)))))))

(tu/deftest-kb a-markdown-fence-is-stripped
  (testing "models fence unprompted — even while decoding under a schema that cannot express one"
    (let [{:keys [rows]} (session/parse-lines
                          "Here you go:\n```\n[(dog Muffet) WellContext]\n```")]
      (is (= 1 (count rows)))
      (is (= ['(dog Muffet) 'WellContext] (:entry (first rows))))))
  (testing "including a ```json fence around the other shape"
    (let [{:keys [rows]} (session/parse-lines
                          (str "```json\n"
                               (json/generate-string
                                {"lines" [{"sentence" "(dog Muffet)" "context" "WellContext"}]})
                               "\n```"))]
      (is (= ['(dog Muffet) 'WellContext] (:entry (first rows)))))))

(tu/deftest-kb a-json-envelope-is-tolerated-not-required
  (let [{:keys [rows notes]}
        (session/parse-lines
         (json/generate-string
          {"lines" [{"sentence" "(dog Muffet)" "context" "WellContext"}
                    {"sentence" "(parentOf Tom Ann)" "context" "WellContext"
                     "strength" "monotonic"}]
           "notes" "unsure about Ann"}))]
    (is (= 2 (count rows)))
    (is (= ['(parentOf Tom Ann) 'WellContext {:strength :monotonic}] (:entry (second rows))))
    (is (= "unsure about Ann" notes))))

(tu/deftest-kb prose-around-the-lines-becomes-notes
  (let [{:keys [rows notes]} (session/parse-lines
                              (str "I have rewritten the first line.\n\n"
                                   "[(fatherOf Tom Ann) WellContext]\n"
                                   "[(dog Muffet) WellContext]\n\n"
                                   "Let me know if that is right."))]
    (is (= 2 (count rows)))
    (testing "prose is the only commentary channel the line format has, so it is kept"
      (is (str/includes? notes "rewritten the first line"))
      (is (str/includes? notes "Let me know")))))

(tu/deftest-kb parse-lines-reports-what-it-cannot-read
  (testing "prose and nothing else is an error, not an empty line set — an empty line set is a mass retraction"
    (is (seq (:errors (session/parse-lines "Ann is a veterinarian.")))))
  (testing "a line that starts like an entry and is not one is an error, never a silent drop"
    (is (seq (:errors (session/parse-lines "[(dog Muffet) WellContext]\n[(dog"))))
    (is (seq (:errors (session/parse-lines "[(dog Muffet)]"))))
    (is (seq (:errors (session/parse-lines "[(dog Muffet) \"WellContext\"]")))))
  (testing "and so is a JSON envelope whose entries do not read"
    (is (seq (:errors (session/parse-lines
                       (json/generate-string
                        {"lines" [{"sentence" "(dog" "context" "WellContext"}]})))))))

(tu/deftest-kb parse-lines-cannot-evaluate-code
  (testing "a line is read as EDN, which has no reader-eval"
    (is (seq (:errors (session/parse-lines "[#=(clojure.core/println \"pwned\") WellContext]"))))))

(tu/deftest-kb the-output-schema-is-an-object-per-line
  (testing "when a caller opts into it, a bare string per line is what it must not be"
    (let [items (get-in sel/output-schema ["properties" "lines" "items"])]
      (is (= "object" (get items "type")))
      (is (= #{"sentence" "context"} (set (get items "required"))))
      (is (contains? (get items "properties") "strength")))))

(tu/deftest-kb the-prompt-demonstrates-the-formalism
  (testing "a small model coins new content in the shape it was shown, not the one it was told"
    (is (str/includes? sel/system-prompt "[(fatherOf Tom Ann) WellContext]"))
    (is (str/includes? sel/system-prompt "[(ownedBy Muffet Ann) WellContext]")
        "including a line invented from nothing, which is the weak case")))

;; ---- the content diff ---------------------------------------------------

(tu/deftest-kb an-unchanged-line-touches-nothing
  (let [{:keys [h-parent h-dog]} (world kb)
        rows (sel/selected kb [h-parent h-dog])
        same (mapv (fn [r] {:key (:key r) :entry (vec (:key r))}) rows)]
    (is (= {:add [] :remove []} (session/diff-batch rows same)))))

(tu/deftest-kb a-rewrite-retracts-the-old-and-asserts-the-new
  (let [{:keys [h-parent h-dog fatherOf Tom Ann ctx]} (world kb)
        rows (sel/selected kb [h-parent h-dog])
        new  [{:key [(list fatherOf Tom Ann) ctx] :entry [(list fatherOf Tom Ann) ctx]}
              {:key (:key (second rows)) :entry (vec (:key (second rows)))}]
        {:keys [add remove]} (session/diff-batch rows new)]
    (is (= [h-parent] remove) "only the rewritten line's handle is retracted")
    (is (= [[(list fatherOf Tom Ann) ctx]] add))))

(tu/deftest-kb a-dropped-line-is-a-retraction-and-the-summary-says-so
  (let [{:keys [h-parent h-dog]} (world kb)
        rows  (sel/selected kb [h-parent h-dog])
        kept  [{:key (:key (first rows)) :entry (vec (:key (first rows)))}]
        batch (session/diff-batch rows kept)]
    (is (= [h-dog] (:remove batch)))
    (is (= {:selected 2 :returned 1 :unchanged 1 :removed 1 :added 0}
           (session/edit-summary rows kept batch)))))

;; ---- propose-edit, end to end against the stub --------------------------

(tu/deftest-kb propose-edit-answers-a-reviewable-batch-and-textarea-lines
  (let [{:keys [h-parent h-dog fatherOf Tom Ann ctx]} (world kb)
        dog-line (:line (first (sel/selected kb [h-dog])))
        p (stub/provider {:script [{:lines [[(list fatherOf Tom Ann) ctx]
                                            (edn/read-string dog-line)]
                                    :notes "made it specific"}]})
        r (session/propose-edit kb {:handles [h-parent h-dog] :message "be specific"
                                    :provider p})]
    (is (= :ok (:status r)))
    (is (= [[(list fatherOf Tom Ann) ctx]] (:add (:batch r))))
    (is (= [h-parent] (:remove (:batch r))))
    (is (= "made it specific" (:notes r)))
    (is (= {:selected 2 :returned 2 :unchanged 1 :removed 1 :added 1} (:summary r)))
    (testing ":lines is what a browser panel drops into the open editor"
      (is (= 2 (count (str/split-lines (:lines r)))))
      (is (every? #(vector? (edn/read-string %)) (str/split-lines (:lines r)))))))

(tu/deftest-kb proposing-never-writes
  (let [{:keys [h-parent h-dog fatherOf Tom Ann ctx]} (world kb)
        before (set (map :id (v/sentexes-in-context kb ctx)))
        p (stub/provider {:script [{:lines [[(list fatherOf Tom Ann) ctx]]}]})
        r (session/propose-edit kb {:handles [h-parent h-dog] :message "rewrite"
                                    :provider p})]
    (is (= :ok (:status r)))
    (is (seq (:remove (:batch r))) "the batch does propose retractions")
    (is (= before (set (map :id (v/sentexes-in-context kb ctx))))
        "…and not one of them happened")))

(tu/deftest-kb the-critic-runs-on-the-selection-path-too
  (let [{:keys [h-dog ctx]} (world kb)
        bad (list 'NotAPredicate 'Muffet)
        p (stub/provider {:script (repeat 3 {:lines [[bad ctx]]})})
        r (session/propose-edit kb {:handles [h-dog] :message "break it" :provider p})]
    (is (= :invalid (:status r)))
    (is (= :naming (:type (first (:rejections r)))))
    (testing "and it fed the rejection back before giving up"
      (is (= 3 (:attempts r)))
      (is (str/includes? (stub/last-user-text p) "naming")))))

(tu/deftest-kb an-unreadable-answer-is-repaired-then-reported
  (let [{:keys [h-dog]} (world kb)
        p (stub/provider {:script ["not json at all" "still not json" "nor this"]})
        r (session/propose-edit kb {:handles [h-dog] :message "x" :provider p})]
    (is (= :unparseable (:status r)))
    (is (= 3 (:attempts r)))
    (is (str/includes? (stub/last-user-text p) "rejected"))))

(tu/deftest-kb an-oversized-selection-sends-nothing
  (let [{:keys [h-parent h-dog]} (world kb)
        p (stub/provider {})
        r (session/propose-edit kb {:handles [h-parent h-dog] :message "x"
                                    :provider p :num-ctx 16})]
    (is (= :too-large (:status r)))
    (is (str/includes? (:text r) "does not fit"))
    (is (neg? (:headroom (:budget r))))
    (testing "the request was never made — a truncated selection is the one failure a reviewer cannot see"
      (is (empty? (stub/requests p))))))

(tu/deftest-kb an-empty-selection-is-its-own-status
  (let [p (stub/provider {})
        r (session/propose-edit kb {:handles [999999] :message "x" :provider p})]
    (is (= :empty-selection (:status r)))
    (is (empty? (stub/requests p)))))

(tu/deftest-kb the-request-carries-no-tools-and-no-schema-by-default
  (let [{:keys [h-dog ctx dog Muffet]} (world kb)
        p (stub/provider {:script [{:lines [[(list dog Muffet) ctx]]}]})
        _ (session/propose-edit kb {:handles [h-dog] :message "x" :provider p :num-ctx 4096})
        req (first (stub/requests p))]
    (is (empty? (:tools req)) "a completion-only model cannot use a tool schema")
    (is (nil? (:format req))
        "`format` is not portable across models, so the line format is the contract")
    (is (= 4096 (:num-ctx req)))
    (testing "the selection and the card ride in the user turn"
      (is (str/includes? (:content (first (:messages req))) "Selected lines"))
      (is (str/includes? (:content (first (:messages req))) "Vocabulary")))))

(tu/deftest-kb a-schema-is-sent-only-when-a-caller-asks-for-it
  (let [{:keys [h-dog ctx dog Muffet]} (world kb)
        p (stub/provider {:script [{:lines [[(list dog Muffet) ctx]] :json? true}]})
        r (session/propose-edit kb {:handles [h-dog] :message "x" :provider p
                                    :format sel/output-schema})]
    (is (= sel/output-schema (:format (first (stub/requests p)))))
    (testing "and the JSON the model then answers with parses just as well"
      (is (= :ok (:status r)))
      (is (= {:add [] :remove []} (:batch r))))))

(tu/deftest-kb an-applied-proposal-reaches-storage-only-through-the-explicit-call
  (let [{:keys [h-parent h-dog fatherOf Tom Ann ctx]} (world kb)
        dog-line (:line (first (sel/selected kb [h-dog])))
        p (stub/provider {:script [{:lines [[(list fatherOf Tom Ann) ctx]
                                            (edn/read-string dog-line)]}]})
        r (session/propose-edit kb {:handles [h-parent h-dog] :message "x" :provider p})]
    (is (= :ok (:status r)))
    (session/apply-proposal! kb r)
    (is (seq (v/sentexes-matching kb (list fatherOf Tom Ann) ctx)) "the rewrite landed")
    (is (nil? (v/sentex kb h-parent)) "and the original was retracted")))

;; ---- the provider seam --------------------------------------------------

(tu/deftest-kb the-stub-is-the-default-and-the-fallback
  ;; **This opens no socket, on any machine.**  `(provider/provider)` with no kind reads
  ;; `configured` — `VAELII_LLM_PROVIDER` / `-Dvaelii.llm.provider` — so on a machine that
  ;; names a real backend there, an unmarked test in `:default` would probe it; and
  ;; naming `:ollama` outright probes the host whatever the environment says.  A
  ;; reachable Ollama is not consent (`docs/llm.md`), so the selection is pinned instead
  ;; of read.  What is under test here is the *fallback*, not a model, which is why this
  ;; belongs in `:default` rather than behind `^:llm`.
  (is (true? (provider/available? :stub)))
  (testing "nothing configured is the stub — that is what makes the pipeline testable"
    (with-redefs [provider/configured (constantly nil)]
      (is (satisfies? proto/Provider (provider/provider)))
      (is (= :stub (provider/active-kind)))))
  (testing "a configured backend this build cannot reach degrades to the stub rather
            than throwing"
    (with-redefs [provider/configured (constantly :nonesuch)]
      (is (satisfies? proto/Provider (provider/provider)))
      (is (= :stub (provider/active-kind)))))
  (testing "and one that probes available but will not build degrades the same way —
            the caller gets a Provider, never nil and never an exception"
    (with-redefs [provider/available? (constantly true)
                  provider/build      (constantly nil)]
      (is (satisfies? proto/Provider (provider/provider :ollama)))))
  (testing "a kind nobody implements is simply not available, and asking for it anyway
            still answers with a Provider"
    (is (false? (provider/available? :nonesuch)))
    (is (satisfies? proto/Provider (provider/provider :nonesuch)))))

;; ---- the Ollama backend, offline ----------------------------------------

(tu/deftest-kb a-host-is-normalized-not-guessed
  (is (= "http://ollama.example:11434" (ollama/normalize-host "ollama.example:11434")))
  (is (= "http://ollama.example:11434" (ollama/normalize-host "http://ollama.example:11434/")))
  (is (= "https://x.example" (ollama/normalize-host "https://x.example"))))

(tu/deftest-kb the-request-body-is-ollamas-shape
  (let [b (ollama/body {:system [{:text "sys" :cache? true}]
                        :messages [{:role "user" :content "hi"}]
                        :format {"type" "object"}
                        :num-ctx 2048
                        :max-tokens 512}
                       {:stream? false})]
    (is (= "system" (get-in b ["messages" 0 "role"])))
    (is (= "sys" (get-in b ["messages" 0 "content"]))
        "the cache flag is dropped — a local model has no prefix cache to break on")
    (is (= "hi" (get-in b ["messages" 1 "content"])))
    (is (= 2048 (get-in b ["options" "num_ctx"])))
    (is (= 512 (get-in b ["options" "num_predict"])))
    (is (= 0.0 (get-in b ["options" "temperature"])) "a proposal is reproducible by default")
    (is (= {"type" "object"} (get b "format")))
    (is (false? (get b "stream")))
    (is (not (contains? b "tools")) "no tools key at all when none are sent")))

(tu/deftest-kb a-response-becomes-the-neutral-shape
  (let [r (ollama/parse-response
           {"model" "phi4:14b" "done" true "done_reason" "stop"
            "message" {"role" "assistant" "content" "{\"lines\":[]}"}
            "prompt_eval_count" 580 "eval_count" 132 "eval_duration" 1548000000})]
    (is (= "end_turn" (:stop-reason r)))
    (is (= "{\"lines\":[]}" (proto/text r)))
    (is (= 580 (:input-tokens (:usage r))))
    (is (= 1548 (:eval-ms (:usage r)))))
  (testing "a cut-off answer is max_tokens, so a caller can tell it from a finished one"
    (is (= "max_tokens" (:stop-reason (ollama/parse-response
                                       {"done_reason" "length" "message" {"content" "…"}})))))
  (testing "and a tool-capable model's calls come back as tool-use blocks"
    (let [r (ollama/parse-response
             {"done_reason" "stop"
              "message" {"content" ""
                         "tool_calls" [{"function" {"name" "kb_types_of"
                                                    "arguments" {"x" "Muffet"}}}]}})]
      (is (= "tool_use" (:stop-reason r)))
      (is (= "kb_types_of" (:name (first (proto/tool-uses r))))))))

;; ---- live: a real Ollama ------------------------------------------------

(defn- live-model
  "The model the live tests run against, or nil with a printed reason.  Opting in is
  checked **first**, before the host is so much as probed; then reachability **and**
  model presence, because a host that is up but has never pulled the model fails in a
  way that reads like a bug in this code."
  []
  (let [model (ollama/configured-model)]
    (cond
      (not (tu/live-llm?))
      (do (println "  [skip] live Ollama tests: set VAELII_LLM_LIVE=1 to opt in") nil)

      (not (ollama/available? {:timeout-ms 2000}))
      (do (println (str "  [skip] live Ollama tests: no server at " (ollama/base-url)
                        " — set VAELII_OLLAMA_HOST to point at one"))
          nil)

      (nil? (ollama/capabilities model))
      (do (println (str "  [skip] live Ollama tests: " (ollama/base-url) " has no model "
                        model " — set VAELII_OLLAMA_MODEL"))
          nil)

      :else model)))

(tu/deftest-kb ^:llm a-live-model-reports-what-it-can-do
  (when-let [model (live-model)]
    (let [caps (ollama/capabilities model)]
      (is (contains? caps :completion))
      (is (= (contains? caps :tools) (ollama/supports-tools? model))
          "supports-tools? is exactly the declared capability, not a guess")
      (is (pos? (or (ollama/context-length model) 0))))))

(tu/deftest-kb ^:llm a-live-model-edits-a-selection
  (when-let [model (live-model)]
    (let [{:keys [h-parent h-dog fatherOf dog Muffet]} (world kb)
          p (ollama/provider {:model model :keep-alive "5m"})
          r (session/propose-edit
             kb {:handles [h-parent h-dog] :provider p :num-ctx 8192
                 :message (str "The parent named in these lines is male. Restate that line "
                               "with the most specific predicate the vocabulary offers. "
                               "Leave every other line exactly as it is.")})]
      (is (contains? #{:ok :invalid} (:status r))
          (str "unexpected status " (:status r) " — " (pr-str (:text r))))
      (when (= 1 (:attempts r))
        (testing "the host's measured prompt is under the estimate the budget refused on"
          (is (<= (:input-tokens (:usage r)) (:prompt (:budget r))))))
      (when (= :ok (:status r))
        (testing "it reached for the sub-predicate the card offered"
          (is (str/includes? (:lines r) (str fatherOf))))
        (testing "and left the unrelated line alone"
          (is (str/includes? (:lines r) (pr-str (list dog Muffet)))))
        (testing "proposing still writes nothing"
          (is (some? (v/sentex kb h-parent)))
          (is (some? (v/sentex kb h-dog))))))))

(tu/deftest-kb ^:llm a-live-model-streams-the-same-answer
  (when-let [model (live-model)]
    (let [{:keys [h-dog]} (world kb)
          deltas (atom 0)
          p (ollama/provider {:model model :keep-alive "5m"})
          r (session/propose-edit kb {:handles [h-dog] :provider p
                                      :message "Return the line exactly as given."
                                      :on-event #(when (= :text-delta (:type %))
                                                   (swap! deltas inc))})]
      (is (pos? @deltas) "newline-delimited JSON was reassembled into text deltas")
      (is (contains? #{:ok :invalid :unparseable} (:status r))))))
