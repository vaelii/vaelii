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
  EDN s-expression** — `\"(dog ?x)\"`, `\"CxWell\"` — read back with
  `clojure.edn/read-string` (never `read-string`: EDN has no reader-eval, so a model's
  output cannot evaluate code)."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.impl.serve :as serve]))

;; ---- which ops the model may reach --------------------------------------

(def write-ops
  "The ops in `serve/ops` the model may not reach.  A new mutating op **must** be
  listed here — the exposed tool set is `(keys serve/ops)` minus this, so an omission
  would hand the model a write.  Ops resolving to a `!` var are excluded
  independently, which catches the ones spelled with the warning already.

  That second mechanism is a backstop, not the rule: `!` means *irreversible*
  (`docs/api.md`), and a write that merely mutates is spelled without one.  So every
  mutating op is listed here explicitly, including the ones the `!` sweep cannot see —
  `:edit` and `:edit-with-consequences` both store, and neither carries the suffix.
  `:preview` stores nothing but belongs here all the same: it applies its batch and
  rolls it back, so it holds the process's single writer, advances the handle counter
  and moves the chain and settle statistics — `serve` and `access` both file it with
  the writes for that reason.  `:clear-caches` mutates the process's measurement
  state, which is nothing to hand a model that is being measured through it."
  #{:assert :assert-rule :assert-many :retract :edit :edit-with-consequences
    :forward-chain :preview :clear-caches
    ;; `:abduce` mints its hypotheses through the whole assert pipeline into a scratch
    ;; context, and `:abduce-discard` tears one down; `:add-provenance` stores.  The
    ;; first and the last are spelled without a `!` — provenance is metadata, and an
    ;; abduction without `{:keep? true}` cleans up after itself — so the `!` sweep below
    ;; cannot see either
    :abduce :abduce-discard :add-provenance})

(def host-path-ops
  "Reads the model may not reach for a different reason than `write-ops`: an argument names
  a **path on the daemon's host**, not a value carried on the wire, so exposing the read
  hands the model the host filesystem.  `:kb-diff`'s second side is a directory the daemon
  reads (`serve.clj`), so the reads-only sweep would otherwise generate a `kb_kb_diff` tool
  that loads and diffs an arbitrary host path — a path-recon primitive for a prompt-injected
  model.  `:export` names a host path too but is a write, so its `!` already excludes it;
  this set is the read half the `!` backstop cannot see."
  #{:kb-diff})

(defn- core-var
  "The `vaelii.core` var an op keyword names, or nil."
  [op]
  (ns-resolve 'vaelii.core (symbol (name op))))

(defn- arglists [v] (:arglists (meta v)))

(defn- variadic? [v]
  (boolean (some #(some #{'&} %) (arglists v))))

(defn read-ops
  "The op keywords the model may call: `serve/ops` minus the writes and the host-path
  reads, minus anything that does not resolve to a non-variadic `vaelii.core` var.
  Sorted, so the generated tool list is byte-stable and the prompt cache survives a
  rebuild."
  []
  (->> (set/difference (set (keys serve/ops)) write-ops host-path-ops)
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

(def ^:private by-tool-name
  "Every exposed read keyed by the tool name it answers to.

  Held, because `read-ops` is not a lookup: it walks `serve/ops`, resolves each keyword in
  `vaelii.core` and reads two pieces of metadata off every var it finds — and `op-of` ran
  that whole walk once per tool name, which is once per tool call in a turn that makes a
  dozen.  Both inputs are fixed at load, `serve/ops` being a literal table and an op's
  arglists being its var's metadata, so one walk answers every call."
  (delay (into {} (map (juxt tool-name identity)) (read-ops))))

(defn op-of
  "The op keyword a tool name came from, or nil if it names no exposed read."
  [tname]
  (get @by-tool-name tname))

;; ---- parameter shapes ---------------------------------------------------

(def ^:private integer-params
  '#{handle jid id pos level floor n})

(def ^:private array-params
  '#{terms})

(def ^:private param-doc
  "Per-parameter guidance, keyed by the `vaelii.core` parameter name.  Anything not
  listed falls back to the generic EDN-form description."
  '{sentence "A sentence as an EDN s-expression: \"(dog Muffet)\", \"(parentOf ?x Tom)\"."
    goal     "A goal formula, or a vector of them for a conjunctive query: \"[(parentOf ?x ?y) (dog ?y)]\"."
    context  "A context name: \"CxWell\". Use \"?ctx\" to mean any context."
    ctx      "A context name: \"CxWell\"."
    term     "A single term (predicate, individual, type, or context name): \"Muffet\"."
    terms    "Terms to intersect on, as EDN strings: [\"Muffet\", \"dog\"]."
    handle   "A sentex handle — the integer id a stored sentex is referenced by."
    arg-pos  "Which slot the audit reads: \":second\" for predAllSpecified (the default), \":first\" for the predSpecifiedAll twin. Only those two values."
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
                  "Send context alongside it: the argument shapes nest, so opts with no "
                  "context names the structure that has neither and is refused. "
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
  off one longest arity.

  A `serve/kbless-ops` op keeps its whole list: the daemon supplies a KB to every row of
  its table, but these fns take none, so their first parameter is an argument the caller
  sends (`quality-report`'s reading, `readable-sentence`'s sentex).  Dropping it here
  published a one-argument are indistinguishable from a no-argument tool that then threw on arity."
  [op v]
  (let [drop-kb (if (serve/kbless-ops op) identity rest)]
    (vec (sort-by count (map #(vec (drop-kb %)) (arglists v))))))

(defn- op-params
  "`[all required]` for an op: every parameter any signature takes (first-seen order),
  and the ones **every** signature takes."
  [op v]
  (let [sigs (signatures op v)
        all  (vec (distinct (apply concat sigs)))]
    [all (filterv (fn [p] (every? #(some #{p} %) sigs)) all)]))

(defn schema
  "The tool schema for one op keyword."
  [op]
  (let [v (core-var op)
        sigs (signatures op v)
        [all required] (op-params op v)
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
  "Every exposed are indistinguishable from a tool schema, in `read-ops` order.  `opts`:

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
  "Project records to plain maps, so a result prints as something the model can read.

  **A lazy stream stays lazy wherever it sits** — projected element by element rather
  than walked whole — because what prints it is bounded (`bounded-pr-str`):
  `kb_sentexes_in_context` over an imported ontology answers a hundred thousand records,
  and only the first few dozen ever reach the 4,000 characters the model is shown.
  Realizing a stream here to project it would fetch and project every one of them to keep
  that prefix.

  Which is why this is a walk of its own rather than `clojure.walk/postwalk`, and why the
  test is `seq?` rather than a `LazySeq` type test.  `postwalk` is depth-first and eager,
  so a stream one level down — `{:rows …}`, or behind a `cons` — is realized whole before
  the bounded writer ever runs; and `(cycle …)`, `(iterate …)` and `(repeat …)` are not
  `LazySeq` at all, so under a type test the walker is handed a seq with no end and the
  read dies of memory instead of answering its first few dozen elements.

  A record is projected before the map branch can see it: a record is an
  `IPersistentMap`, but `empty` on one throws."
  [x]
  (cond
    (record? x) (reduce-kv (fn [m k v] (assoc m k (wire-safe v))) {} x)
    (seq? x)    (map wire-safe x)
    (map? x)    (reduce-kv (fn [m k v] (assoc m (wire-safe k) (wire-safe v))) (empty x) x)
    (vector? x) (mapv wire-safe x)
    (set? x)    (into (empty x) (map wire-safe) x)
    :else       x))

(defn- bounded-pr-str
  "`pr-str` of `x`, written into a sink that stops at `limit` characters: `[s cut?]`,
  where `s` holds exactly `limit` characters of the printing when `cut?` is true and all
  of it otherwise.

  The bound is on the *writer*, which is the only place it can be: `pr` realizes a lazy
  answer as it prints, so a writer that refuses the character past the limit is what
  stops a broad read from realizing — and printing — megabytes to keep four kilobytes.
  The stop is a throw from inside `pr`, caught here; nothing else sees it.

  **The clip is inside the write rather than a check after it.**  One `print-method` call
  can hand over a whole string in one go — a symbol's name, an object's `str` — so a bound
  tested afterwards is really `limit` plus the longest single write, which is the megabyte
  the bound exists to refuse.  Each write appends the room that is left, and then stops."
  [x limit]
  (let [sb    (StringBuilder.)
        lim   (long limit)
        stop  (ex-info "over the result bound" {::over true})
        room  (fn [] (- lim (.length sb)))
        put-s (fn [^CharSequence s ^long off ^long len]
                (let [r (long (room))]
                  (if (<= len r)
                    (.append sb s (int off) (int (+ off len)))
                    (do (when (pos? r) (.append sb s (int off) (int (+ off r))))
                        (throw stop)))))
        put-a (fn [^chars c ^long off ^long len]
                (let [r (long (room))]
                  (if (<= len r)
                    (.append sb c (int off) (int len))
                    (do (when (pos? r) (.append sb c (int off) (int r)))
                        (throw stop)))))
        sink  (proxy [java.io.Writer] []
                (write
                  ([c] (if (string? c)
                         (put-s c 0 (count c))
                         (if (pos? (long (room)))
                           (.append sb (char c))
                           (throw stop))))
                  ([c off len]
                   (if (string? c)
                     (put-s c off len)
                     (put-a c off len))))
                (flush [])
                (close []))]
    (try
      (binding [*out* sink] (pr x))
      [(str sb) false]
      (catch clojure.lang.ExceptionInfo e
        (if (identical? e stop)
          [(str sb) true]
          (throw e))))))

(defn- coerce
  "JSON value -> the value `vaelii.core` wants.  A string argument is an EDN form
  unless the parameter is declared integer; an array is read element-wise."
  [p v]
  (cond
    (integer-params p) (long v)
    (array-params p)   (mapv #(if (string? %) (edn/read-string %) %) v)
    (string? v)        (edn/read-string v)
    :else              v))

(defn- render
  "`x` as the string a `tool_result` carries: its printing, cut at `limit` characters and
  marked as cut when there was more.  The cut happens in the writer, so a result the
  model sees four kilobytes of was never printed — or realized — past them, and what
  comes back cut is already exactly `limit` characters long."
  [x limit]
  (let [[s cut?] (bounded-pr-str x limit)]
    (if cut?
      (str s "\n… [truncated at " limit " characters]")
      s)))

(defn call
  "Run one tool call against `kb` and return `{:ok true :result \"…\"}` or
  `{:ok false :error \"…\"}` — the string a `tool_result` block carries back.

  `input` is the provider's JSON object (string keys).  The **longest signature the
  input fully satisfies** decides the call, so an op with several shapes (`why-not`
  takes a handle *or* a sentence and a context) dispatches to the one the model
  actually supplied.  Dispatch goes through `serve/ops`, the same table the schemas
  were generated from.

  **An argument the chosen signature does not take is refused, never dropped.**  The
  shapes nest — `query` takes `(goal)`, `(goal, context)`, `(goal, context, opts)` —
  so an input of goal *and* opts with no context satisfies only the first, and passing
  it on would answer facts-only with the depth discarded, which reads exactly like a
  goal no rule can reach.  That is `opts/check!`'s failure one level out: an argument
  nothing reads takes the default in silence.  So the refusal names the form the
  input selected and the shapes the op has, and the model supplies the argument in
  between.

  Never throws: a bad argument, an unknown tool, or a refusal from the KB comes back
  as `{:ok false :error \"…\"}`, which is what a `tool_result` block wants — the model
  reads the error and tries again.

  `opts`: `:max-result-chars` (default 4000) bounds what a broad read can push into
  the context window."
  ([kb tname input] (call kb tname input {}))
  ([kb tname input {:keys [max-result-chars] :or {max-result-chars 4000}}]
   (if-let [op (op-of tname)]
     (let [sigs   (signatures op (core-var op))
           sig    (last (filter (fn [s] (every? #(contains? input (name %)) s)) sigs))
           shapes (str/join " or " (map #(str "(" (str/join ", " %) ")") sigs))
           unread (when sig (sort (remove (set (map name sig)) (keys input))))]
       (cond
         (nil? sig)
         {:ok false
          :error (str "missing arguments — " tname " takes " shapes)}

         (seq unread)
         {:ok false
          :error (str tname " cannot read " (str/join ", " unread)
                      " beside the arguments given: they select the shape ("
                      (str/join ", " (map name sig)) "), and " tname " takes "
                      shapes ".  A shape is chosen by what is supplied, so give"
                      " every argument of the one you want.")}

         :else
         (try
           (let [args (mapv (fn [p] (coerce p (get input (name p)))) sig)]
             {:ok true
              :result (render (wire-safe ((serve/ops op) kb args)) max-result-chars)})
           ;; `Throwable`, as every other read of a model's output: `coerce` reads a
           ;; string argument as EDN, and a deeply nested form overflows the reader's
           ;; stack with a `StackOverflowError`, which an `Exception` catch lets escape
           ;; — out of a fn documented never to throw, and up into the turn loop, where
           ;; a bad argument is the ordinary answer this exists to give.
           ;; The class name when there is no message, as `session/parse-batch` does: a
           ;; `StackOverflowError` carries none, so `.getMessage` is nil and the arm that
           ;; exists to name the failure hands the model `{:error ""}` — a refusal that
           ;; says nothing, which is indistinguishable from a tool that answered emptily rather than from an
           ;; argument it should fix.
           (catch Throwable e
             {:ok false
              :error (str (or (ex-message e) (.getName (class e)))
                          (when-let [t (:type (ex-data e))] (str " [" t "]")))}))))
     {:ok false :error (str "unknown tool: " tname)})))
