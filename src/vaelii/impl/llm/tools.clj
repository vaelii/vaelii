;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.tools
  "The model's read surface over a KB — **generated**, not hand-written.

  `vaelii.impl.serve/ops` is already an allowlisted, EDN-typed map of `vaelii.core`
  calls: the exact surface the browser and the daemon reach a KB through.  So the
  tool schemas are derived from its **read subset** rather than transcribed, and the
  tool calls are dispatched back through the same table.  A read added to `serve/ops`
  becomes a tool with no edit here; a read renamed there cannot rot a copy here,
  because there is no copy.

  **The model never writes.**  `write-ops` names every mutating op, and anything
  resolving to a `!` var is treated as one whatever the table says, so the exposed set
  is reads only.  The model's *output* is a proposed batch, reviewed and applied by a
  human (`vaelii.impl.llm.session`) — there is no write tool and no write path.

  Argument shapes come from the `vaelii.core` var's own `:arglists` (minus the leading
  `kb`) and its docstring, so a signature change is picked up on the next build.  JSON
  carries no symbols, so a sentence / context / term argument is a **string holding an
  EDN s-expression** — `\"(dog ?x)\"`, `\"WellContext\"` — read back with
  `clojure.edn/read-string` (never `read-string`: EDN has no reader-eval, so a model's
  output cannot evaluate code)."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [vaelii.impl.serve :as serve]))

;; ---- which ops the model may reach --------------------------------------

(def write-ops
  "The mutating ops in `serve/ops`.  A new mutating op **must** be listed here — the
  exposed tool set is `(keys serve/ops)` minus this, so an omission would hand the
  model a write.  Ops resolving to a `!` var are excluded independently, which catches
  the ones spelled with the warning already.

  That second mechanism is a backstop, not the rule: `!` means *irreversible*
  (`docs/api.md`), and a write that merely mutates is spelled without one.  So every
  mutating op is listed here explicitly, including the ones the `!` sweep cannot see —
  `:edit` and `:edit-with-consequences` both store, and neither carries the suffix."
  #{:assert :assert-rule :assert-many :retract :edit :edit-with-consequences
    :forward-chain})

(defn- core-var
  "The `vaelii.core` var an op keyword names, or nil."
  [op]
  (ns-resolve 'vaelii.core (symbol (name op))))

(defn- arglists [v] (:arglists (meta v)))

(defn- variadic? [v]
  (boolean (some #(some #{'&} %) (arglists v))))

(defn read-ops
  "The op keywords the model may call: `serve/ops` minus the writes, minus anything
  that does not resolve to a non-variadic `vaelii.core` var.  Sorted, so the generated
  tool list is byte-stable and the prompt cache survives a rebuild."
  []
  (->> (set/difference (set (keys serve/ops)) write-ops)
       (filter (fn [op]
                 (when-let [v (core-var op)]
                   (and (not (str/ends-with? (name (:name (meta v))) "!"))
                        (not (variadic? v))))))
       sort
       vec))

;; ---- op keyword <-> tool name -------------------------------------------
;; A tool name is `[a-zA-Z0-9_-]{1,128}`, so `?` has to go; `_p` keeps `ask?` and
;; `ask` distinct instead of colliding on a bare truncation.

(defn tool-name
  "The tool name for an op keyword — `:find-sentexes` -> `kb_find_sentexes`,
  `:ask?` -> `kb_ask_p`."
  [op]
  (str "kb_" (-> (name op) (str/replace "-" "_") (str/replace "?" "_p"))))

(defn op-of
  "The op keyword a tool name came from, or nil if it names no exposed read."
  [tname]
  (first (filter #(= tname (tool-name %)) (read-ops))))

;; ---- parameter shapes ---------------------------------------------------

(def ^:private integer-params
  '#{handle jid id pos level floor n})

(def ^:private array-params
  '#{terms})

(def ^:private param-doc
  "Per-parameter guidance, keyed by the `vaelii.core` parameter name.  Anything not
  listed falls back to the generic EDN-form description."
  '{sentence "A sentence as an EDN s-expression: \"(dog Muffet)\", \"(parentOf ?x Tom)\"."
    goal     "A goal sentence, or a vector of them for a conjunctive query: \"[(parentOf ?x ?y) (dog ?y)]\"."
    context  "A context name: \"WellContext\". Use \"?ctx\" to mean any context."
    ctx      "A context name: \"WellContext\"."
    term     "A single term (predicate, individual, type, or context name): \"Muffet\"."
    terms    "Terms to intersect on, as EDN strings: [\"Muffet\", \"dog\"]."
    handle   "A sentex handle — the integer id a stored sentex is referenced by."
    jid      "A justification id."
    x        "An individual: \"Muffet\"."
    t        "A type: \"dog\"."
    sub      "The more specific type: \"dog\"."
    super    "The more general type: \"animal\"."
    pred     "A predicate name: \"parentOf\"."
    functor  "A predicate or type name — the head of a sentence."
    kind     "A predicate property: \":transitive\", \":symmetric\", \":reflexive\", \":functional\"."
    pos      "A 1-based argument position."
    level    "A retrieval level, 0 (raw index) to 7 (full backchaining)."
    floor    "The lowest level to start climbing from (default 2)."
    q        "A search string matched against term names."
    opts     (str "Options map, as an EDN string. For kb_query and kb_query_p this is "
                  "where the rule-expansion depth goes: \"{:max-depth 3}\". With no "
                  "depth the read expands no rule at all and answers only from stored "
                  "facts and cached closures — which is a real answer, not an error, so "
                  "pass a depth when the conclusion you want follows from rules. "
                  "Elsewhere, per-op options such as \"{:limit 20}\".")})

(defn- param-schema [p]
  (let [desc (or (param-doc p)
                 (str "The `" p "` argument, as an EDN string."))]
    (cond
      (integer-params p) {"type" "integer" "description" desc}
      (array-params p)   {"type" "array" "items" {"type" "string"} "description" desc}
      :else              {"type" "string" "description" desc})))

(defn- summary
  "The first paragraph of a docstring, whitespace-collapsed — enough for the model to
  choose a tool, without pasting the whole essay into every request."
  [v]
  (let [d (or (:doc (meta v)) "")]
    (-> (first (str/split d #"\n\s*\n"))
        (str/replace #"\s+" " ")
        str/trim)))

(defn- signatures
  "The op's parameter lists, minus the leading `kb`, shortest first.  An op can have
  genuinely *different* shapes rather than nested ones — `why-not` takes `[handle]` or
  `[sentence context]` — so a schema and a call must both work off the whole set, not
  off one longest arity."
  [v]
  (vec (sort-by count (map #(vec (rest %)) (arglists v)))))

(defn- op-params
  "`[all required]` for an op: every parameter any signature takes (first-seen order),
  and the ones **every** signature takes."
  [v]
  (let [sigs (signatures v)
        all  (vec (distinct (apply concat sigs)))]
    [all (filterv (fn [p] (every? #(some #{p} %) sigs)) all)]))

(defn schema
  "The tool schema for one op keyword."
  [op]
  (let [v (core-var op)
        sigs (signatures v)
        [all required] (op-params v)
        doc (summary v)
        doc (if (str/blank? doc) (str "Read `" (name op) "` from the knowledge base.") doc)
        doc (if (next sigs)
              (str doc " Argument sets: "
                   (str/join " | " (map #(str "(" (str/join ", " %) ")") sigs)) ".")
              doc)]
    (cond-> {"name" (tool-name op)
             "description" doc
             "input_schema" {"type" "object"
                             "properties" (into {} (map (fn [p] [(name p) (param-schema p)])) all)
                             "required" (mapv name required)
                             "additionalProperties" false}}
      ;; Strict tool use guarantees the input validates against the schema exactly, so
      ;; a hallucinated extra argument is caught before it reaches `call`.  Claimed
      ;; only for an op with one signature: a strict schema requires every declared
      ;; property, and an op like `isa?` deliberately has one it can do without.
      (= (count all) (count required)) (assoc "strict" true))))

(defn schemas
  "Every exposed read as a tool schema, in `read-ops` order.  `opts`:

    :only     a set of op keywords to keep (default: all reads)
    :exclude  a set of op keywords to drop"
  ([] (schemas {}))
  ([{:keys [only exclude]}]
   (->> (read-ops)
        (filter (fn [op] (and (or (nil? only) (contains? only op))
                              (not (contains? (or exclude #{}) op)))))
        (mapv schema))))

;; ---- dispatch -----------------------------------------------------------

(defn- wire-safe
  "Project records to plain maps and realize lazy seqs, so a result `pr-str`s to
  something the model can read (and a lazy answer stream is realized before it is
  truncated)."
  [x]
  (walk/postwalk (fn [y] (if (record? y) (into {} y) y)) x))

(defn- coerce
  "JSON value -> the value `vaelii.core` wants.  A string argument is an EDN form
  unless the parameter is declared integer; an array is read element-wise."
  [p v]
  (cond
    (integer-params p) (long v)
    (array-params p)   (mapv #(if (string? %) (edn/read-string %) %) v)
    (string? v)        (edn/read-string v)
    :else              v))

(defn- truncate [s limit]
  (if (<= (count s) limit)
    s
    (str (subs s 0 limit) "\n… [truncated at " limit " characters]")))

(defn call
  "Run one tool call against `kb` and return `{:ok true :result \"…\"}` or
  `{:ok false :error \"…\"}` — the string a `tool_result` block carries back.

  `input` is the provider's JSON object (string keys).  The **longest signature the
  input fully satisfies** decides the call, so an op with several shapes (`why-not`
  takes a handle *or* a sentence and a context) dispatches to the one the model
  actually supplied.  Dispatch goes through `serve/ops`, the same table the schemas
  were generated from.

  Never throws: a bad argument, an unknown tool, or a refusal from the KB comes back
  as `{:ok false :error \"…\"}`, which is what a `tool_result` block wants — the model
  reads the error and tries again.

  `opts`: `:max-result-chars` (default 4000) bounds what a broad read can push into
  the context window."
  ([kb tname input] (call kb tname input {}))
  ([kb tname input {:keys [max-result-chars] :or {max-result-chars 4000}}]
   (if-let [op (op-of tname)]
     (let [sigs (signatures (core-var op))
           sig  (last (filter (fn [s] (every? #(contains? input (name %)) s)) sigs))]
       (if (nil? sig)
         {:ok false
          :error (str "missing arguments — " tname " takes "
                      (str/join " or " (map #(str "(" (str/join ", " %) ")") sigs)))}
         (try
           (let [args (mapv (fn [p] (coerce p (get input (name p)))) sig)]
             {:ok true
              :result (truncate (pr-str (wire-safe ((serve/ops op) kb args))) max-result-chars)})
           (catch Exception e
             {:ok false
              :error (str (.getMessage e)
                          (when-let [t (:type (ex-data e))] (str " [" t "]")))}))))
     {:ok false :error (str "unknown tool: " tname)})))
