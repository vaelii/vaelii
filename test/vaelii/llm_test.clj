;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.llm-test
  "The pluggable LLM that proposes KB edits (`vaelii.host.llm.*`).

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
            [vaelii.host.llm.anthropic :as anthropic]
            [vaelii.host.llm.http :as llm-http]
            [vaelii.host.llm.ollama :as ollama]
            [vaelii.host.llm.prompt :as prompt]
            [vaelii.host.llm.protocol :as proto]
            [vaelii.host.llm.session :as session]
            [vaelii.host.llm.stub :as stub]
            [vaelii.host.llm.tools :as tools]
            [vaelii.host.serve :as serve]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- tool schemas are generated from serve/ops --------------------------

(deftest the-writer-holding-ops-are-filed-with-the-writes
  ;; the subset test below is relative, so it cannot see these two leak: `:preview`
  ;; stores nothing but applies its batch and rolls it back under the process's
  ;; single writer, and `:clear-caches` mutates process measurement state.  Neither
  ;; ends in `!`, so the backstop cannot catch them either — the roster is the entry point.
  (is (contains? tools/write-ops :preview))
  (is (contains? tools/write-ops :clear-caches)))

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
        (is (not (contains? reads w)))))
    (testing "a host-path read is served for a human caller but kept out of the model's tools"
      (is (seq tools/host-path-ops) "the host-path exclusion set is not empty")
      (is (contains? tools/host-path-ops :kb-diff)
          "kb-diff's second side is a path on the daemon's host")
      (doseq [h tools/host-path-ops]
        (is (contains? serve/ops h)
            (str h " is excluded as a host-path read but serve does not serve it"))
        (is (not (contains? reads h))
            (str h " names a host path and must not become a model tool"))))))

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
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (testing "a query returns the stored sentence"
      (let [{:keys [ok result]} (tools/call kb "kb_sentexes_matching" {"sentence" (pr-str (list dog '?x))})]
        (is ok)
        (is (str/includes? result (str Muffet)))))
    (testing "an integer parameter arrives as an integer"
      (let [h (v/handle-of kb (list dog Muffet) 'CxUniverse)
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
    (testing "an argument the chosen shape cannot read is refused, never dropped"
      ;; The shapes nest — `query` takes (goal), (goal, context), (goal, context, opts) —
      ;; so goal-plus-opts satisfies only the first.  Handed on, the depth would be
      ;; discarded and the read would answer facts-only, which reads exactly like a goal
      ;; no rule can reach: `opts/check!`'s silent default, one level further out.
      (let [{:keys [ok error]} (tools/call kb "kb_query" {"goal" (pr-str (list animal '?x))
                                                          "opts" "{:max-depth 3}"})]
        (is (false? ok))
        (is (str/includes? error "opts"))
        (is (str/includes? error "(goal)")))
      (testing "and the same call with the argument in between is run"
        (let [{:keys [ok]} (tools/call kb "kb_query" {"goal" (pr-str (list animal '?x))
                                                      "context" "?ctx"
                                                      "opts" "{:max-depth 3}"})]
          (is ok)))
      (testing "the two disjoint shapes of why-not refuse a mixture rather than picking"
        (let [{:keys [ok error]} (tools/call kb "kb_why_not"
                                             {"handle" 1
                                              "sentence" (pr-str (list dog Muffet))
                                              "context" "CxUniverse"})]
          (is (false? ok))
          (is (str/includes? error "handle")))))
    (testing "results are bounded"
      (let [{:keys [result]} (tools/call kb "kb_terms" {} {:max-result-chars 20})]
        (is (str/includes? result "truncated"))
        (is (= 20 (count (first (str/split-lines result)))) "cut at the bound exactly")))
    (testing "and the bound is on the printing, so a broad read realizes only what it shows
              — the op below never ends, and a reader that printed it whole would not either"
      (let [realized (atom 0)
            endless  (map (fn [i] (swap! realized inc)
                            {:id i :sentence (list 'dog 'Muffet) :context 'CxEndless})
                          (range))]
        (with-redefs [serve/ops (assoc serve/ops :sentexes-in-context (fn [_ _] endless))]
          (let [{:keys [ok result]} (tools/call kb "kb_sentexes_in_context" {"context" "CxEndless"}
                                                {:max-result-chars 300})]
            (is ok)
            (is (str/includes? result "truncated at 300"))
            (is (str/starts-with? result "({:id 0"))
            (is (< @realized 200) (str @realized " records realized to show 300 characters"))))))))

(tu/deftest-kb a-stream-stays-lazy-wherever-it-sits-in-the-answer
  ;; A `LazySeq` test only ever caught the top-level case, and a depth-first walk
  ;; underneath it realized the rest: an op answering `{:rows <stream>}`, or anything
  ;; behind a `cons`, was walked whole before the bounded writer ran.  And `cycle`,
  ;; `iterate` and `repeat` are not `LazySeq` at all, so a seq with no end was handed to
  ;; the walker and the read died of memory rather than answering its first few dozen.
  (let [shapes {"a bare stream"      identity
                "a stream in a map"  (fn [s] {:rows s})
                "a stream in a list" (fn [s] (list :head s))
                "a stream behind a cons" (fn [s] (cons :head s))
                "a stream in a vector"   (fn [s] [:head s])}]
    (doseq [[label wrap] shapes]
      (let [realized (atom 0)
            endless  (map (fn [i] (swap! realized inc) {:id i}) (range))]
        (with-redefs [serve/ops (assoc serve/ops :sentexes-in-context
                                       (fn [_ _] (wrap endless)))]
          (let [{:keys [ok result]} (tools/call kb "kb_sentexes_in_context" {"context" "CxEndless"}
                                                {:max-result-chars 300})]
            (is ok label)
            (is (str/includes? result "truncated at 300") label)
            (is (< @realized 500) (str label ": " @realized " elements realized for 300 characters")))))))
  (testing "and a seq that is not a LazySeq is bounded the same way"
    ;; each of these hangs — or dies of memory — under a walk that realizes to project
    (doseq [[label answer] {"cycle"        (cycle [1 2])
                            "iterate"      (iterate inc 0)
                            "repeat"       (repeat :x)
                            "a nested cycle" {:rows (cycle [1 2])}}]
      (with-redefs [serve/ops (assoc serve/ops :sentexes-in-context (fn [_ _] answer))]
        (let [{:keys [ok result]} (tools/call kb "kb_sentexes_in_context" {"context" "CxEndless"}
                                              {:max-result-chars 300})]
          (is ok label)
          (is (str/includes? result "truncated at 300") label))))))

(deftest one-write-cannot-carry-the-result-past-its-bound
  ;; The bound was tested *after* each write, so what it really held was `limit` plus the
  ;; longest single write — and one `print-method` call hands over a whole string: a
  ;; symbol's name, an object's `str`.  A term four hundred thousand characters long is
  ;; the memory the bound exists to refuse, appended whole to keep three hundred of it.
  ;; Read off the writer rather than off `render`, since `render` cut the oversized
  ;; buffer back down and the answer looked right either way.
  (let [bounded  @#'tools/bounded-pr-str
        long-sym (symbol (apply str (repeat 400000 \x)))]
    (doseq [[label x] {"a symbol printed in one write" [long-sym]
                       "a string printed character by character" [(apply str (repeat 400000 \y))]
                       "an unbounded stream"           (range 100000)}]
      (let [[s cut?] (bounded x 300)]
        (is cut? label)
        (is (= 300 (count s))
            (str label ": the writer kept " (count s) " characters to bound the result at 300"))))
    (testing "and a printing that fits is not cut at all"
      (let [[s cut?] (bounded [:a :b] 300)]
        (is (not cut?))
        (is (= "[:a :b]" s))))))

(tu/deftest-kb a-failure-with-no-message-is-still-named
  ;; The `Throwable` catch is there because `coerce` reads a model's argument as EDN and a
  ;; deeply nested form overflows the reader's stack.  A `StackOverflowError` carries **no
  ;; message**, so the arm that exists to name the failure would hand the model an empty
  ;; string — a refusal saying nothing, which is indistinguishable from a tool that answered emptily rather
  ;; than as an argument to fix.
  (doseq [[label thrown expected]
          [["an Error with no message" (StackOverflowError.) "java.lang.StackOverflowError"]
           ["an Exception with no message" (RuntimeException.) "java.lang.RuntimeException"]
           ["and one that has a message keeps it" (RuntimeException. "no such term") "no such term"]]]
    (testing label
      (let [{:keys [ok error]}
            (with-redefs [serve/ops (assoc serve/ops :terms (fn [_ _] (throw thrown)))]
              (tools/call kb "kb_terms" {}))]
        (is (false? ok))
        (is (= expected error))
        (is (not (str/blank? error)) "an empty error is not a diagnosis")))))

;; ---- the system prompt is generated from the KB -------------------------

(tu/deftest-kb system-prompt-reads-the-live-kb
  (tu/with-terms [dog animal Muffet CxStory]
    (let [before (prompt/system-prompt kb)]
      (is (not (str/includes? before (str dog))))
      (v/assert kb (list 'genl dog animal) 'CxUniverse)
      (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse)
      (v/assert kb (list dog Muffet) CxStory)
      (let [after (prompt/system-prompt kb)]
        (is (str/includes? after (str dog)) "a new type reaches the prompt")
        (is (str/includes? after (str CxStory)) "a new context reaches the prompt")
        (is (str/includes? after "Naming invariants"))
        (is (str/includes? after ":add"))
        (is (= after (prompt/system-prompt kb)) "generation is deterministic")
        (is (not= before after))))))

(tu/deftest-kb system-prompt-carries-argisa-and-disjointness
  (tu/with-terms [dog cat parentOf Muffet]
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 1 dog) 'CxUniverse)
    (let [p (prompt/system-prompt kb)]
      (is (str/includes? p "Disjointness"))
      (is (str/includes? p (str dog)))
      (is (str/includes? p (str parentOf)))
      (is (str/includes? p (str "1:`" dog "`")) "arg reaches the predicate line"))))

;; ---- parsing a proposed batch -------------------------------------------

(deftest parse-batch-reads-the-last-fenced-block
  (testing "a fenced edn block"
    (is (= {:add [] :remove []}
           (:batch (session/parse-batch "here you go\n\n```edn\n{:add [] :remove []}\n```")))))
  (testing "the last block wins — a model often shows a draft first"
    (is (= {:add [['(dog Muffet) 'CxWell]] :remove []}
           (:batch (session/parse-batch
                    (str "draft:\n```edn\n{:add [] :remove []}\n```\n"
                         "final:\n```edn\n{:add [[(dog Muffet) CxWell]]}\n```"))))))
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
    (let [rs (session/check-batch kb {:add [[(list 'BadFunctor Muffet) 'CxUniverse]]
                                      :remove []})]
      (is (= 1 (count rs)))
      (is (= :naming (:type (first rs))))
      (is (= :add (:in (first rs))))
      (is (str/includes? (:message (first rs)) "functor")))))

(tu/deftest-kb a-non-ground-fact-is-a-not-ground-rejection
  (tu/with-terms [mortal]
    (let [rs (session/check-batch kb {:add [[(list mortal '?x) 'CxUniverse]] :remove []})]
      (is (= 1 (count rs)))
      (is (= :not-ground (:type (first rs)))))))

(tu/deftest-kb a-disjoint-clash-is-a-disjoint-rejection
  (tu/with-terms [dog cat Muffet]
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [rs (session/check-batch kb {:add [[(list cat Muffet) 'CxUniverse]] :remove []})]
      (is (= 1 (count rs)))
      (is (= :disjoint (:type (first rs))))))
  (testing "the critic did not store the entry it rejected"
    (tu/with-terms [dog cat Muffet]
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (session/check-batch kb {:add [[(list cat Muffet) 'CxUniverse]] :remove []})
      (is (nil? (v/handle-of kb (list cat Muffet) 'CxUniverse))
          "checking must not write"))))

(tu/deftest-kb an-argisa-clash-is-an-arg-type-rejection
  ;; Pinned to the constraint reading: the classification asserted is :arg-type, and with
  ;; the entailment on the same content is refused as the :disjoint clash the mint makes
  ;; (docs/argtypes.md).
  (tu/without-entailing
   (tu/with-terms [dog cat likes Muffet Whiskers]
     (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
     (v/assert kb (list 'genl cat 'thing) 'CxUniverse)
     (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
     (v/assert kb (list 'arg likes 1 dog) 'CxUniverse)
     (v/assert kb (list cat Whiskers) 'CxUniverse)
     (let [rs (session/check-batch kb {:add [[(list likes Whiskers Muffet) 'CxUniverse]]
                                       :remove []})]
       (is (= 1 (count rs)))
       (is (= :arg-type (:type (first rs))))))))

(tu/deftest-kb malformed-entries-and-handles-are-rejected
  (testing "an entry that is not [sentence context]"
    (is (= :shape (:type (first (session/check-batch kb {:add ['(dog Muffet)] :remove []}))))))
  (testing "a context that is not a symbol"
    (is (= :shape (:type (first (session/check-batch
                                 kb {:add [['(dog Muffet) "CxWell"]] :remove []}))))))
  (testing "a removal naming no stored sentex"
    (let [rs (session/check-batch kb {:add [] :remove [999999]})]
      (is (= :unknown-handle (:type (first rs))))
      (is (= :remove (:in (first rs))))))
  (testing "a removal naming a stored one is fine"
    (tu/with-terms [dog Muffet]
      (let [h (v/assert kb (list dog Muffet) 'CxUniverse)]
        (is (empty? (session/check-batch kb {:add [] :remove [h]})))))))

(tu/deftest-kb a-well-formed-batch-has-no-rejections
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (is (empty? (session/check-batch kb {:add [[(list dog Muffet) 'CxUniverse]]
                                         :remove []})))))

;; ---- the repair loop ----------------------------------------------------

(tu/deftest-kb the-loop-repairs-a-rejected-batch
  (tu/with-terms [dog Muffet]
    (let [p (stub/provider
             {:script [{:batch {:add [[(list 'BadFunctor Muffet) 'CxUniverse]] :remove []}}
                       {:batch {:add [[(list dog Muffet) 'CxUniverse]] :remove []}}]})
          result (session/propose kb {:message "add Muffet as a dog" :provider p})]
      (is (= :ok (:status result)))
      (is (= 2 (:attempts result)) "one rejected batch, one accepted")
      (is (= {:add [[(list dog Muffet) 'CxUniverse]] :remove []} (:batch result)))
      (testing "the critic's typed verdict is what was fed back"
        (is (str/includes? (stub/last-user-text p) ":naming"))
        (is (str/includes? (stub/last-user-text p) "BadFunctor"))))))

(tu/deftest-kb the-loop-gives-up-cleanly-when-repair-fails
  (tu/with-terms [Muffet]
    (let [bad {:batch {:add [[(list 'BadFunctor Muffet) 'CxUniverse]] :remove []}}
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
    (v/assert kb (list dog Muffet) 'CxUniverse)
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
          batch {:add [[(list dog Muffet) 'CxUniverse]] :remove []}
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
          batch {:add [[(list dog Muffet) 'CxUniverse]] :remove []}
          p (stub/provider {:script [{:batch batch}]})
          proposal (session/propose kb {:message "add Muffet" :provider p})]
      (is (= :ok (:status proposal)))
      (is (= before (tu/sentex-ids kb))
          "proposing stored nothing — the model has no write path")
      (is (nil? (v/handle-of kb (list dog Muffet) 'CxUniverse)))
      (testing "the explicit apply is what writes"
        (let [applied (session/apply-proposal! kb proposal)]
          (is (= 1 (count (:added (:result applied)))))
          (is (some? (v/handle-of kb (list dog Muffet) 'CxUniverse)))
          (is (empty? (:violations applied))))))))

(tu/deftest-kb apply-refuses-a-proposal-the-critic-rejected
  (tu/with-terms [Muffet]
    (let [bad {:batch {:add [[(list 'BadFunctor Muffet) 'CxUniverse]] :remove []}}
          p (stub/provider {:script [bad bad bad] :default (:batch bad)})
          proposal (session/propose kb {:message "x" :provider p :max-repairs 1})]
      (is (= :invalid (:status proposal)))
      (is (thrown? clojure.lang.ExceptionInfo (session/apply-proposal! kb proposal)))
      (is (= :llm-not-applicable
             (try (session/apply-proposal! kb proposal)
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))))

(tu/deftest-kb apply-round-trips-a-removal
  (tu/with-terms [dog Muffet]
    (let [h (v/assert kb (list dog Muffet) 'CxUniverse)
          p (stub/provider {:script [{:batch {:add [] :remove [h]}}]})
          proposal (session/propose kb {:message "drop it" :provider p})]
      (is (= :ok (:status proposal)))
      (is (some? (v/handle-of kb (list dog Muffet) 'CxUniverse)) "still there after proposing")
      (session/apply-proposal! kb proposal)
      (is (nil? (v/handle-of kb (list dog Muffet) 'CxUniverse))))))

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

(deftest a-content-block-the-encoder-cannot-shape-is-refused-rather-than-dropped
  ;; The refusal is for a block this namespace has no JSON shape for.  Encoded as nothing
  ;; it would send a turn missing a block the rest of the turn refers to, and the API's
  ;; own complaint would name neither the turn nor the block; encoded as a guess it would
  ;; send an edited thinking block, which the API rejects outright.  A pure encode — no
  ;; request is built, no credential is read and no host is reached.
  (let [encode #'anthropic/encode-block]
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (encode {:type :thinking :thinking "weighing it"})))]
      (is (= :llm-encode (:type (ex-data e))))
      (is (= :thinking (:block-type (ex-data e)))
          "and it names the type it could not shape, which is what a caller acts on"))
    (testing "a block that came off a response carries its original JSON and rides back
              unchanged, whatever its type — which is why the refusal is for the built
              ones alone"
      (is (= {"type" "thinking" "thinking" "weighing it" "signature" "sig"}
             (encode {:type :thinking
                      :raw {"type" "thinking" "thinking" "weighing it" "signature" "sig"}}))))
    (testing "and the three shapes it does model encode without one"
      (is (= {"type" "text" "text" "checking"} (encode {:type :text :text "checking"}))))))

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

;; ---- what the two transports refuse, and how ----------------------------
;; Both backends are checked in one place because what is under test is the vocabulary
;; they share: a credential that cannot ride in a header, a 200 whose body is not JSON,
;; and a host that goes quiet with the body half-read.  None of it opens a socket — a
;; request is *built* rather than sent, and the deadline is exercised with the read
;; stubbed.

(deftest a-credential-that-cannot-ride-in-a-header-is-refused-without-quoting-it
  (let [conn (fn [v] {:base-url "http://127.0.0.1:1" :timeout-ms 1000
                      :credential {:kind :api-key :value v}})]
    (doseq [[what value] [["a trailing CRLF, which is what a .env file leaves"
                           "sk-ant-SUPERSECRET\r\n"]
                          ["a control character mid-string, which no trim removes"
                           (str "sk-ant-" (char 7) "SUPERSECRET")]]]
      (testing what
        (let [e (try (#'anthropic/request-builder (conn value) {"model" "m"} [])
                     nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (some? e) "the JDK rejects the value, and the rejection does not escape raw")
          (is (= :llm-bad-credential (:type (ex-data e))))
          (is (= "x-api-key" (:header (ex-data e))) "the header is named")
          (testing "and the value is in neither the message nor the data: the JDK's own
                    exception quotes it verbatim, and an error message reaches the page"
            (is (not (str/includes? (str (ex-message e) " " (pr-str (ex-data e)))
                                    "SUPERSECRET")))))))
    (testing "a credential with nothing wrong with it still builds a request"
      (is (some? (#'anthropic/request-builder (conn "sk-ant-ordinary") {"model" "m"} []))))))

(deftest an-environment-credential-is-trimmed
  (testing "the whitespace a shell or a .env file leaves is not part of the value"
    (is (= "sk-ant-x" (#'anthropic/clean "  sk-ant-x \r\n")))
    (is (nil? (#'anthropic/clean "   ")))
    (is (nil? (#'anthropic/clean nil)))))

(deftest a-body-that-is-not-json-carries-a-type-like-every-other-refusal
  (doseq [[backend decode] [["anthropic" #'anthropic/decode] ["ollama" #'ollama/decode]]]
    (testing backend
      (let [e (try (decode "<html>a proxy answered</html>" 200) nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e))
        (is (= :llm-bad-response (:type (ex-data e))) "a caller discriminates on the keyword")
        (is (= 200 (:status (ex-data e)))))
      (testing "and the excerpt is bounded, because a response can be megabytes"
        (let [e (try (decode (apply str (repeat 5000 "x")) 200) nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (>= 200 (count (:excerpt (ex-data e)))))
          (is (not (str/includes? (ex-message e) "xxxx"))
              "the body is data, not the message"))))))

(deftest the-connect-deadline-is-not-the-turns-budget
  ;; Two different things: `:timeout-ms` bounds the **answer** and is minutes long by
  ;; design (a cold 14B load, a high-effort turn), while a connection either completes in
  ;; well under a second or is not going to.  Handed the turn's budget, `connectTimeout`
  ;; makes a host that never answers the SYN cost five or ten minutes of a caller's
  ;; thread — a hang wearing a timeout's clothes.
  (testing "the shared deadline is seconds, not minutes"
    (is (<= 1000 llm-http/connect-timeout-ms 10000)))
  (testing "and a client built for a five-minute turn still connects on that deadline"
    (let [^java.net.http.HttpClient c (#'ollama/new-client)]
      (is (= (java.time.Duration/ofMillis llm-http/connect-timeout-ms)
             (.orElse (.connectTimeout c) nil))
          "the connect deadline is the constant, whatever a turn was allowed")))
  (testing "the Anthropic backend reads the same constant — one deadline policy, one place"
    (is (str/includes? (slurp (io/file "src/vaelii/host/llm/anthropic.clj"))
                       "(.connectTimeout b (Duration/ofMillis (long http/connect-timeout-ms)))"))))

(deftest the-probes-share-one-http-client
  ;; A client owns a connection pool and a selector thread.  `available?` runs on every
  ;; `/propose` the browser posts, so a client per probe is a pool per request, each
  ;; answering once and left to the collector.
  ;;
  ;; **This opens no socket.**  The host is a string no URI can be made of, so each probe
  ;; takes its client and then throws in `URI/create` — which `version` catches and
  ;; answers nil to, exactly as it does for a host that is down.
  (let [built (atom 0)]
    (with-redefs [ollama/probe-client (delay (swap! built inc) (#'ollama/new-client))]
      (is (nil? (ollama/version {:host "not a url"})))
      (is (nil? (ollama/version {:host "not a url"})))
      (is (= 1 @built) "two probes, one client")
      (testing "and the probes above available? are the same client again"
        (is (nil? (ollama/capabilities "nonesuch" {:host "not a url"})))
        (is (= 1 @built))))))

(deftest an-error-body-rides-bounded-in-the-message-and-whole-in-the-data
  ;; A failing status carries whatever the far end wrote, and what wrote it is often not
  ;; the API: a proxy in front of it answers megabytes of HTML.  Unbounded in the message,
  ;; that megabyte is in every log line the failure reaches — so the message takes
  ;; `http/excerpt`'s 200 chars and the whole text rides under `:body`, exactly as
  ;; `http/decode`'s `:excerpt` already does for a 200 that would not parse.
  (let [big (apply str (repeat 10000 \x))]
    (doseq [[label api-error prefix json-body]
            [["ollama"    #'ollama/api-error    "Ollama API"
              (str "{\"error\": \"" big "\"}")]
             ["anthropic" #'anthropic/api-error "Anthropic API"
              (str "{\"error\": {\"type\": \"overloaded_error\", \"message\": \"" big "\"}}")]]]
      (testing label
        (testing "a body that is not JSON at all — the proxy case"
          (let [e (api-error 502 big)]
            (is (= :llm-api-error (:type (ex-data e))))
            (is (= 502 (:status (ex-data e))))
            (is (str/starts-with? (ex-message e) (str prefix " 502: ")))
            (is (>= 250 (count (ex-message e)))
                "the message is the excerpt, not the body")
            (is (= big (:body (ex-data e)))
                "and the whole 10 KB is there for a caller that asks for it")))
        (testing "and a JSON body whose own error text is the megabyte"
          (let [e (api-error 529 json-body)]
            (is (>= 250 (count (ex-message e))))
            (is (= json-body (:body (ex-data e))))))))))

(deftest an-error-out-of-the-body-read-is-reported-like-any-other-failure
  ;; What `f` does is parse bytes a far end chose, so the failures it raises are not all
  ;; `Exception`s — a deeply nested body overflows the stack, an oversized one exhausts the
  ;; heap.  Caught narrowly, one raised after the watchdog closed the body escaped as
  ;; itself, and a caller's `:llm-timeout` handler saw a `StackOverflowError` instead.
  (let [endpoint {:label "the test endpoint" :slug "error-arm"}
        under    (partial llm-http/under-read-deadline endpoint)
        alive?   (fn [] (some (fn [^Thread t]
                                (and (.isAlive t)
                                     (= "vaelii-error-arm-deadline" (.getName t))))
                              (keys (Thread/getAllStackTraces))))]
    (testing "an Error raised after the deadline fired takes the :llm-timeout rewrite"
      (let [closed (promise)
            e (try (under 20 #(deliver closed true)
                          (fn []
                            (deref closed 5000 :never)
                            (throw (StackOverflowError. "a body nested past the stack"))))
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (realized? closed) "the watchdog fired")
        (is (some? e) "and the Error was rewritten rather than left to escape as itself")
        (is (= :llm-timeout (:type (ex-data e))))
        (is (instance? StackOverflowError (ex-cause e)) "the Error rides as the cause")))
    (testing "with the deadline unspent the Error is the caller's and propagates unchanged"
      (is (thrown? StackOverflowError
                   (under 60000 (fn [] nil)
                          (fn [] (throw (StackOverflowError. "a body nested past the stack")))))))
    (testing "and the watchdog is cancelled on the way out, whichever arm was taken"
      (loop [tries 50]                                   ; the interrupt lands promptly
        (when (and (alive?) (pos? tries))
          (Thread/sleep 10)
          (recur (dec tries))))
      (is (not (alive?))
          "no 60-second watchdog left running behind an Error that propagated"))))

(deftest a-host-that-goes-quiet-mid-body-releases-the-thread
  ;; The request's own `.timeout` bounds the response *arriving*; a streamed turn is read
  ;; off the socket after that, and the browser's page path always streams.  So the body
  ;; read carries its own deadline, and this is that deadline: the watchdog closes the
  ;; body, and the failure which follows is a typed timeout rather than whatever I/O
  ;; error a closed socket raises.
  ;; One deadline, not one per provider: `llm-http/under-read-deadline` is what both the
  ;; Anthropic and the Ollama stream paths call, so exercising it twice would exercise
  ;; the same function twice.  The endpoint descriptor is the only thing each supplies,
  ;; and it names the far end in the message rather than changing what happens.
  (let [endpoint {:label "the test endpoint" :slug "test"}
        under    (partial llm-http/under-read-deadline endpoint)]
    (let [closed (promise)
          e (try (under 20 #(deliver closed true)
                        ;; stands in for a read blocked on a socket nobody is writing
                        ;; to: it ends when the watchdog closes the body under it
                        (fn []
                          (deref closed 5000 :never)
                          (throw (java.io.IOException. "stream closed"))))
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (realized? closed) "the watchdog fired and closed the body")
      (is (= :llm-timeout (:type (ex-data e))))
      (is (= 20 (:timeout-ms (ex-data e))))
      (is (str/includes? (ex-message e) "the test endpoint")
          "and the message names the far end that went quiet"))
    (testing "a failure with the deadline unspent belongs to the caller and is rethrown"
      (is (thrown? java.io.IOException
                   (under 60000 (fn [] nil)
                          (fn [] (throw (java.io.IOException. "connection reset")))))))
    (testing "and a read that finishes hands back what it read"
      (is (= :read-it (under 60000 (fn [] nil) (fn [] :read-it)))))))

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
;;
;; Agreeing is not the whole claim, though, and the gap is the one a *new* test falls
;; into.  Mark ⟺ gate says the two decorations move together; it says nothing about a
;; test that carries **neither** and reaches a host anyway.  Such a test is consistent
;; with both directions of the check and runs under a plain `lein test`.  So the third
;; scan below reads what a test *calls*: a host probe, or a real backend built and then
;; driven, is reaching — and a reaching test must be marked or must have pinned the var
;; it reaches through.

(def ^:private gate-call
  "What consulting the consent gate looks like in a source file: a **call** to
  `live-llm?` under any alias.

  Anchored on the structure of a call — an open paren, then the name, then a delimiter — and
  not on the bare name, so this does not match the prose around it or its own failure
  messages.  A scanner that flags its own source is worse than no scanner, since the way
  to make it green is to stop saying what it checks.  The delimiter is a class rather
  than a close paren: a gate helper that takes an argument is still the gate."
  #"\([\w.-]*/?live-llm\?[\s)]")

(defn- top-level-starts
  "The index of every top-level form in a source file — a `(` in column zero."
  [src]
  (vec (keep-indexed (fn [i c] (when (and (= \( c) (or (zero? i) (= \newline (nth src (dec i)))))
                                 i))
                     src)))

(defn- top-level-forms
  "Every top-level form in a source file, as the source text of each.

  Split on column-zero openers rather than read, since what is under test is the **source**
  a reader edits: a mark dropped from the text is the failure mode, and `read`ing the file
  would resolve it away.  A form runs to the next **top-level form**, so a helper defined
  between two tests belongs to neither — taking it as part of the one before it is how this
  check first reported two tests that dial out and do not."
  [path]
  (let [src    (slurp path)
        starts (top-level-starts src)]
    (mapv #(subs src %1 %2) starts (concat (rest starts) [(count src)]))))

(defn- bound-name
  "The name a top-level `def…` form binds, or nil for a form that binds nothing."
  [form]
  (second (re-find #"^\(def\S*\s+(?:\^\S+\s+)*([^\s()]+)" form)))

(defn- call-of
  "A pattern matching a call to `nm`: the name in functor position, never in prose.  The
  qualifier is optional, so a helper hoisted into another namespace is recognised through
  whatever alias the caller gave it — `(live-model …)` and `(tu/live-model …)` are the
  same call."
  [nm]
  (re-pattern (str "\\((?:[\\w.-]+/)?" (java.util.regex.Pattern/quote nm) "[\\s)]")))

(defn- consenting-names
  "The names these forms define whose own source **reaches** the consent gate — a
  `live-llm?` call in the body, or a call to another name in this set.

  A helper is what sits between a live test and the gate, so a test routing through one
  never mentions the gate in its own body and the check has to follow the call.  Following
  it is the whole point: proof of consent is a **path to `live-llm?`**, so a helper that
  merely is indistinguishable from a gated one proves nothing, and a bare provider constructor cannot be
  mistaken for the gate however it is named.  Closed to a fixpoint, so a helper two hops
  out counts too — and the hops cross files: `seed` carries in the names `test_util.clj`
  hoisted (`hoisted-consenting`), so a local helper calling one of *those* is reached by
  the same closure rather than having to be named the same thing."
  ([forms] (consenting-names forms #{}))
  ([forms seed]
   (let [defs (into {} (keep (fn [f] (when-let [nm (bound-name f)] [nm f]))) forms)]
     (loop [ok (into (set seed) (keep (fn [[nm f]] (when (re-find gate-call f) nm)) defs))]
       (let [grown (into ok
                         (keep (fn [[nm f]] (when (some #(re-find (call-of %) f) ok) nm)))
                         defs)]
         (if (= grown ok) ok (recur grown)))))))

;; ---- what reaching a provider looks like in a source file ---------------
;; The roster is written in full namespace names and translated per file through that
;; file's own `:require` aliases, because a test names a namespace however it likes and a
;; scan keyed on the conventional alias would miss the file that spelled it differently.

(def ^:private probe-calls
  "Calls that open a socket to a model host **by themselves**.  Every one of these is an
  HTTP request the moment it is evaluated, so one in a test body is a dial-out however the
  result is used.

  **The `provider` extension point's three selecting entry points are here, not below.**  Each asks
  `provider/available?` before it builds anything, and for `:ollama` that probes the host
  — so on a machine whose `VAELII_LLM_PROVIDER` names a real backend, `(provider/provider)`
  with no kind dials, and `(provider/provider :ollama)` dials whatever the environment
  says.  `VAELII_LLM_PROVIDER` is configuration, never consent (the consent gate is
  `VAELII_LLM_LIVE`, read through `tu/live-llm?`), so a test reaching one of these pins a
  `transport-extension-point` — which is what `the-stub-is-the-default-and-the-fallback` and
  `a-backend-that-probes-available-and-then-throws-is-logged` already do."
  '#{vaelii.host.llm.ollama/version
     vaelii.host.llm.ollama/available?
     vaelii.host.llm.ollama/show
     vaelii.host.llm.ollama/capabilities
     vaelii.host.llm.ollama/supports-tools?
     vaelii.host.llm.ollama/context-length
     vaelii.host.llm.ollama/warm
     vaelii.host.llm.provider/warm
     vaelii.host.llm.provider/provider
     vaelii.host.llm.provider/generation-provider
     vaelii.host.llm.provider/active-kind})

(def ^:private backend-constructors
  "Calls that hand back a provider bound to a **real** backend.  None of these opens a
  socket on its own — building an Ollama provider is a map and a `reify`, and
  `provider/build` goes straight to the constructor without probing — so one of them
  alone is not a dial-out, and several tests in `:default` build one deliberately to check
  what happens when a credential is missing or a constructor throws."
  '#{vaelii.host.llm.ollama/provider
     vaelii.host.llm.ollama/generation-provider
     vaelii.host.llm.anthropic/provider
     vaelii.host.llm.provider/build})

(def ^:private turn-drivers
  "Calls that run a turn against whatever provider they are handed.  Harmless over the
  stub, which is how most of this suite uses them — it is the **pair** that dials: a real
  backend built, and then driven."
  '#{vaelii.host.llm.session/propose
     vaelii.host.llm.session/propose-edit
     vaelii.host.llm.session/propose-page
     vaelii.host.llm.session/propose-text
     vaelii.host.llm.oracle/judge
     vaelii.host.llm.oracle/judge-batch
     vaelii.host.llm.protocol/complete
     vaelii.host.llm.protocol/stream})

(defn- require-aliases
  "The `alias -> namespace` map a file's `:require` declares."
  [src]
  (into {} (for [[_ nsname al] (re-seq #"\[([\w.-]+)\s+:as\s+([\w.-]+)\]" src)]
             [al nsname])))

(defn- spellings
  "Every way `v` can be written as a call in a file with these aliases — its full name, and
  the alias this file bound its namespace to."
  [by-alias v]
  (let [nsn (namespace v) nm (name v)]
    (cons (str nsn "/" nm)
          (for [[al target] by-alias :when (= target nsn)] (str al "/" nm)))))

(defn- calls-in
  "Which of `vars` this form calls, as the spellings it used."
  [form by-alias vars]
  (into #{} (for [v vars
                  s (spellings by-alias v)
                  :when (re-find (re-pattern (str "\\(" (java.util.regex.Pattern/quote s)
                                                  "[\\s)]"))
                                 form)]
              s)))

(def ^:private transport-extension-points
  "Vars that stand between a roster call and the network.  A test pinning one has taken
  hold of the transport, so what sits above it is exercised rather than dialled —
  `probe-client` *is* the client every Ollama probe sends on, and the `provider` extension point
  decides whether a real backend is built at all."
  '#{vaelii.host.llm.ollama/probe-client
     vaelii.host.llm.provider/configured
     vaelii.host.llm.provider/available?
     vaelii.host.llm.provider/build
     vaelii.host.llm.provider/resolve-fn})

(defn- pinned-in
  "The names a form's `with-redefs` binding vectors mention.  A test that pins the var it
  reaches through has neutralized the reach — `(with-redefs [ollama/available?
  (constantly false)] …)` calls no host.

  Two soft edges, both soft in the same direction: towards a test that has visibly taken
  hold of the extension point rather than one that has not.  The binding is read at the granularity
  of the whole **form** rather than of its scope, so a test that pins a var and also calls
  it outside the `with-redefs` still reads as neutralized.  And a pin on a
  `transport-extension-point` excuses everything above it, which is evidence that the transport is
  the test's rather than proof that no packet leaves."
  [form]
  (set (mapcat (fn [[_ binds]] (re-seq #"[\w.?!*+<>=-]+/[\w.?!*+<>=-]+" binds))
               (re-seq #"with-redefs\*?\s*\[([^\]]*)\]" form))))

(defn- reaching
  "The provider-reaching calls a test form makes, or an empty set.

  Two shapes reach.  A **probe** is a socket on its own.  A **backend constructor** is
  not, so it counts only alongside a call that drives a turn — which is exactly the
  counterexample this scan exists for: build an Ollama provider, hand it to
  `propose-page`, carry no mark, consult no gate, and dial a host under `lein test`.

  A call whose var the form pins with `with-redefs` does not count, and neither does one
  above a pinned `transport-extension-point`.  Nor does reaching through something this cannot see —
  a web route that resolves its own provider is indirection, and `web_propose_test` pins
  `configured` for that reason rather than relying on this."
  [form by-alias]
  (let [pinned  (pinned-in form)
        via-point?  (some (fn [v] (some pinned (spellings by-alias v))) transport-extension-points)
        live    (fn [vars] (remove pinned (calls-in form by-alias vars)))
        probes  (live probe-calls)
        builds  (live backend-constructors)
        drivers (seq (calls-in form by-alias turn-drivers))]
    (if via-point?
      #{}
      (set (concat probes (when drivers builds))))))

(def ^:private test-util-path "test/vaelii/test_util.clj")

(def ^:private hoisted-consenting
  "The gate helpers `vaelii.test-util` defines — the names there whose own source reaches
  `live-llm?`.

  Consent hoisted out of a test file is still consent, and a scan that read only the file
  in front of it would call every test routed through such a helper unconsenting and fail
  the converse check.  `test_util.clj` is the one place helpers are hoisted *to*, so it is
  the one file read beside the test's own."
  (delay (consenting-names (top-level-forms test-util-path))))

(def ^:private llm-metadata
  "The `^:llm` mark, in both spellings a reader may write it: the keyword shorthand and a
  metadata map.  Leiningen reads the merged metadata, so `^{:llm true}` selects exactly as
  `^:llm` does and must count exactly as much."
  #"\^:llm\b|:llm\s+true")

(defn- ns-marked?
  "Does this file's `ns` form carry the mark?  Leiningen merges namespace metadata into
  what a selector reads, so `(ns ^:llm …)` marks every test in the file at once — and a
  per-form scan that missed it would report the whole file as unmarked.

  Read from the **metadata position** only, between `(ns` and the namespace name: a file
  whose docstring explains the mark says `^:llm` in prose, and a scan reading the whole
  form would take every such file for a marked one."
  [path]
  (boolean (some->> (top-level-forms path)
                    (keep #(re-find #"^\(ns\s+((?:\^(?::\S+|\{[^}]*\})\s+)*)[\w.-]+" %))
                    first
                    second
                    (re-find llm-metadata))))

(defn- test-forms
  "Every top-level test in a test file — `deftest`, `tu/deftest-kb` or `defspec` under any
  alias — as `[{:file :name :marked? :consents? :reaches} …]`.  `:consents?` says the body
  reaches `tu/live-llm?`, directly or through a helper this file or `test_util.clj`
  defines; `:reaches` is the provider-reaching calls the body makes that nothing in it
  pins."
  [path]
  (let [forms      (top-level-forms path)
        consenting (consenting-names forms @hoisted-consenting)
        by-alias   (require-aliases (str/join "\n" forms))
        ns-mark?   (ns-marked? path)]
    (for [f forms
          :let [m (re-find #"^\((?:[\w.-]+/)?(?:deftest(?:-kb)?|defspec)\s+((?:\^(?::\S+|\{[^}]*\})\s+)*)([^\s()]+)"
                           f)]
          :when m]
      (let [[_ marks nm] m]
        {:file path
         :name nm
         :marked? (or ns-mark? (boolean (re-find llm-metadata (str marks))))
         :consents? (boolean (or (re-find gate-call f)
                                 (some #(re-find (call-of %) f) consenting)))
         :reaches (reaching f by-alias)}))))

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
    (doseq [{:keys [file name marked? consents?]} @all-tests
            :when consents?]
      (is marked? (str file " / " name " reaches a live model without ^:llm"))))
  (testing "and the converse — a marked test that never consults the gate would run
            against a host on nothing but a selector, which is not consent"
    (doseq [{:keys [file name marked? consents?]} @all-tests
            :when marked?]
      (is consents?
          (str file " / " name " is ^:llm but no path from its body reaches the "
               "live-llm? gate"))))
  (testing "and the case neither direction covers: a test carrying **neither** decoration
            that reaches a provider anyway.  Mark ⟺ gate is satisfied by a test with
            neither, and such a test dials out under a plain `lein test` — so what it
            calls is read too, and a reaching call must be marked or pinned."
    (doseq [{:keys [file name marked? reaches]} @all-tests
            :when (seq reaches)]
      (is marked?
          (str file " / " name " reaches a provider — " (str/join ", " (sort reaches))
               " — with no ^:llm mark and nothing pinning it. Mark it and gate it on "
               "tu/live-llm?, or redefine what it reaches through.")))))

(deftest the-marked-tests-are-the-ones-we-think-they-are
  (testing "a roster, so adding a live test is a visible change rather than a quiet one"
    (is (= #{"a-live-model-reports-what-it-can-do"
             "a-live-model-edits-a-selection"
             "a-live-model-streams-the-same-answer"
             "a-live-model-fleshes-out-a-page"
             "a-live-model-judges-what-the-kb-concluded"
             "the-four-fables-scored-against-their-hand-written-selves"}
           (set (map :name (filter :marked? @all-tests)))))))
