;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.selection
  "The selection-scoped prompt: **the unit of work is a set of handles, not the KB.**

  `vaelii.impl.llm.prompt` renders the whole vocabulary — every context, type and
  predicate — and `vaelii.impl.llm.tools` renders every read as a tool schema.  Both
  are fixed costs that grow with the KB, and against the schema-only starter (no
  individuals, no facts) they already come to ~16,000 tokens before the user has said
  anything — 25,597 characters of system prompt and 31,192 of tool schema, at
  `chars-per-token`.  A KB heading for 100M sentexes cannot pay that per request, and a model
  with no `tools` capability cannot spend half of it at all.

  So this namespace prompts about **what the reader selected**:

  1. the selected sentexes as the editor's own `[sentence context]` lines,
  2. a vocabulary card computed *only* from the terms those lines mention — each
     term's `comment`, its `argIsa` constraints, its place in the genl hierarchy, and
     its metadata,
  3. the reader's instruction.

  Every read is pinned by a term the selection actually contains (`comment-of`, an
  `argIsa` query on a fixed predicate, a genl closure lookup), so the prompt is
  **O(selection)** and flat in KB size.  Ten sentexes cost the same in a KB of ten as
  in a KB of a hundred million.

  **The model rewrites lines; it does not write.**  Its answer is the edited line set,
  which `vaelii.impl.llm.session/propose-edit` diffs against the selection by content
  to produce the `{:add … :remove …}` batch — the same diff the browser's editor does
  on Save, so an unchanged line touches nothing.

  **Nothing here truncates.**  A selection too big for the context window is a clean
  refusal (`budget-problem`), because the alternative is Ollama silently dropping the
  front of the reader's own selection."
  (:require [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]))

;; ---- the editor's line format -------------------------------------------
;; Mirrors what the browser's editor seeds its textarea with, because the proposal
;; lands back in that textarea: the same lines in, the same lines out, and the reader
;; reviews a diff in the format they were already reading.

(defn wrapped-sentence
  "A sentex's editable sentence: the readable sentence (the author's variable names),
  and for a rule its direction / defeasibility spelled back as `set/*Rule` wrappers so
  a re-assert preserves them.  A rule's `exceptWhen` / `unknown` guard lives in a
  separate meta-sentex and is not carried."
  [s]
  (let [base (v/readable-sentence s)]
    (if (:antecedent s)
      (let [d (case (:direction s)
                :forward  (list 'set/forwardRule base)
                :backward (list 'set/backwardRule base)
                :inert    (list 'set/inertRule base)
                base)]
        (if (:defeasible s) (list 'set/defaultRule d) d))
      base)))

(defn edit-line
  "The one editable EDN line for a sentex: `[sentence context]`, plus
  `{:strength :monotonic}` when it is known-true, so a rewrite keeps it."
  [s]
  (let [sent (wrapped-sentence s) ctx (:context s)]
    (if (= :monotonic (:strength s))
      (pr-str [sent ctx {:strength :monotonic}])
      (pr-str [sent ctx]))))

(defn selected
  "The selection as `[{:handle :sentex :key [sentence context] :strength :line \"…\"} …]`,
  in the caller's handle order, silently dropping a handle with no stored sentex (the
  page it was selected on can be older than the KB).  `:key` is the content the diff
  is taken on — the same pair the editor diffs by."
  [kb handles]
  (vec (for [h handles
             :let [s (v/sentex kb h)]
             :when s]
         {:handle h
          :sentex s
          :key [(wrapped-sentence s) (:context s)]
          :strength (:strength s)
          :line (edit-line s)})))

;; ---- the vocabulary card ------------------------------------------------

(defn terms-in
  "Every symbol the selection mentions, plus each line's context — the terms the card
  is computed over.  Variables, numbers and strings carry no vocabulary, so they are
  dropped; nesting depth does not matter, since a term buried in a rule's antecedent
  is as much part of what the reader selected as its consequent's predicate."
  [rows]
  (let [acc (volatile! #{})
        walk (fn walk [form]
               (cond
                 (sequential? form) (run! walk form)
                 (symbol? form)     (when (v/term-role form) (vswap! acc conj form))
                 :else              nil))]
    (doseq [{:keys [key]} rows]
      (walk (first key))
      (walk (second key)))
    @acc))

(defn- collapse [s] (some-> s (str/replace #"\s+" " ") str/trim))

(defn clip
  "A KB string folded to one line and cut to `n` characters — a card is a reminder, not a
  manual.  Public because every prompt section in this package clips the same way, and
  two copies of it would drift apart."
  [s n]
  (let [s (collapse s)]
    (cond (nil? s) nil
          (<= (count s) n) s
          :else (str (subs s 0 n) "…"))))

(defn tick
  "A term in backticks, so a model reads it as a name rather than as prose."
  [x] (str "`" x "`"))

(defn ticks
  "Backticked terms, comma-joined."
  [xs] (str/join ", " (map tick xs)))

(defn- doc-of
  "The term's own documentation, from the `(comment <term> \"…\")` sentexes the
  vocabulary documents itself with — clipped, because a card is a reminder, not a
  manual."
  [kb term max-doc-chars]
  (clip (first (core-context/comment-of kb term)) max-doc-chars))

(defn- argisa-of
  "The `argIsa` constraints on a predicate, as `[[position type] …]`.  The query pins
  the predicate, so this is a narrow read whatever the KB's size."
  [kb pred]
  (sort-by first
           (for [{:keys [sentence]} (v/sentexes-matching kb (list 'argIsa pred '?n '?t) '?ctx)]
             [(nth sentence 2) (nth sentence 3)])))

(defn- disjoint-with
  "The types declared disjoint from `t`, both spellings of the pair."
  [kb t]
  (sort (distinct (concat (for [{:keys [sentence]} (v/sentexes-matching kb (list 'disjoint t '?b) '?ctx)]
                            (nth sentence 2))
                          (for [{:keys [sentence]} (v/sentexes-matching kb (list 'disjoint '?a t) '?ctx)]
                            (nth sentence 1))))))

(defn- props-of
  "The algebraic metadata a predicate carries, as keyword names."
  [kb pred]
  (for [k [:transitive :symmetric :reflexive :functional :universal]
        :when (v/has-prop? kb k pred)]
    (name k)))

(defn- relatives
  "`[genls specs]` for a term, minus the term itself and bounded.  Both are cached
  closure lookups, so this costs nothing even on a deep hierarchy."
  [kb t n]
  [(take n (sort (disj (set (v/genls kb t)) t)))
   (take n (sort (disj (set (v/specs kb t)) t)))])

(defn- functor-entry
  "The card line for a predicate or type: what it means, what its arguments must be,
  where it sits in the hierarchy, and what it is algebraically.  **`specs` matters
  most** — 'state this more specifically' is answerable only if the sub-predicates are
  on the card."
  [kb term {:keys [max-relatives max-doc-chars] :or {max-relatives 12 max-doc-chars 160}}]
  (let [[up down] (relatives kb term max-relatives)
        args (argisa-of kb term)
        dis  (disjoint-with kb term)
        ps   (props-of kb term)
        inv  (v/inverse-of kb term)
        doc  (doc-of kb term max-doc-chars)]
    (str "- " (tick term)
         (when (seq args)
           (str " — args " (str/join ", " (for [[n t] args] (str n ":" (tick t))))))
         (when (seq up)   (str " — is a " (ticks up)))
         (when (seq down) (str " — more specific: " (ticks down)))
         (when (seq dis)  (str " — disjoint from " (ticks dis)))
         (when (seq ps)   (str " — " (str/join ", " ps)))
         (when inv        (str " — inverse of " (tick inv)))
         (when doc        (str " — " doc)))))

(defn- individual-entry
  [kb term {:keys [max-relatives] :or {max-relatives 12}}]
  (let [ts (take max-relatives (sort (v/types-of kb term)))]
    (str "- " (tick term) (when (seq ts) (str " — a " (ticks ts))))))

(defn- context-entry
  [kb term {:keys [max-relatives] :or {max-relatives 12}}]
  (let [up (take max-relatives (sort (disj (set (v/context-up kb term)) term)))]
    (str "- " (tick term) (when (seq up) (str " — sees " (ticks up))))))

(defn- section [heading entries]
  (when (seq entries)
    (str "### " heading "\n" (str/join "\n" entries))))

(defn vocabulary-card
  "The vocabulary the selection actually uses, as markdown.

  Terms are grouped by naming role and each is described from the KB: a
  predicate or type by its `argIsa` constraints, supertypes, **sub-predicates**,
  disjointness, metadata and documentation; an individual by its types; a context by
  what it sees.  Types share the predicate section because they *are* unary predicates
  and `term-role` reads a one-word `dog` as either.  `opts`: `:max-terms` (60),
  `:max-relatives` (12), `:max-doc-chars` (160).

  Nothing here enumerates the KB — every read is pinned by a term the selection
  contains — so the card's size tracks the selection, not the knowledge base."
  ([kb rows] (vocabulary-card kb rows {}))
  ([kb rows {:keys [max-terms] :or {max-terms 60} :as opts}]
   (let [all      (sort (terms-in rows))
         kept     (take max-terms all)
         by-role  (group-by v/term-role kept)
         functors (sort (concat (:predicate by-role) (:type by-role)))]
     (->> [(section "Predicates and types" (map #(functor-entry kb % opts) functors))
           (section "Individuals" (map #(individual-entry kb % opts) (sort (:individual by-role))))
           (section "Contexts" (map #(context-entry kb % opts) (sort (:context by-role))))
           (when (> (count all) max-terms)
             (str "_… and " (- (count all) max-terms) " further terms, not described here._"))]
          (remove str/blank?)
          (str/join "\n\n")))))

;; ---- the output contract ------------------------------------------------

(def output-schema
  "A JSON schema for Ollama's `format` parameter — **an optimization, not the
  contract.**

  `format` is not portable: measured on this task, `phi4:14b` and `qwen2.5-coder:32b`
  honour it, while `qwen3.6:27b` and `nemotron-3-nano:30b` ignore it outright and answer
  in the line format anyway — one of them wrapping its JSON in a markdown fence even
  with the schema set.  So the contract is the **editor's own line format** (which every
  model produces readily, and which makes the round trip through the editor the
  identity), and this schema is opt-in for a model it demonstrably helps.
  `vaelii.impl.llm.session/parse-lines` reads either shape.

  When it is used: an **object per line**, never a bare string.  A free string field
  lets the model choose a shape, and a 14B one quietly drops the enclosing brackets."
  {"type" "object"
   "properties"
   {"lines"
    {"type" "array"
     "description" "The full edited set of lines. Omit a line to delete that sentex."
     "items" {"type" "object"
              "properties" {"sentence" {"type" "string"
                                        "description" "One s-expression, e.g. (fatherOf Tom Ann)"}
                            "context" {"type" "string"
                                       "description" "The context it holds in, e.g. WellContext"}
                            "strength" {"type" "string" "enum" ["monotonic" "default"]
                                        "description" "monotonic = known true; default = defeasible"}}
              "required" ["sentence" "context"]}}
    "notes" {"type" "string"
             "description" "Anything you were unsure of. One or two sentences."}}
   "required" ["lines"]})

;; ---- the two prompt halves ----------------------------------------------

(def ^:private worked-example
  "One input/output pair, shown rather than described.

  A small model is good at *transforming lines it can see* and weak at *coining new
  content* in a formalism it has only been told about: asked to record something new,
  `phi4:14b` answers in English prose while a coder-tuned peer answers in
  s-expressions.  Demonstrating the target formalism — including a line invented from
  nothing — is the cheap fix, and it costs about sixty tokens."
  (str "### Example\n\n"
       "Selected lines:\n\n"
       "[(parentOf Tom Ann) WellContext]\n"
       "[(dog Muffet) WellContext]\n\n"
       "Instruction: Tom is Ann's father, and Muffet belongs to Ann.\n\n"
       "Your whole answer:\n\n"
       "[(fatherOf Tom Ann) WellContext]\n"
       "[(dog Muffet) WellContext]\n"
       "[(ownedBy Muffet Ann) WellContext]\n\n"
       "The first line was rewritten, the second kept exactly as given, the third "
       "invented — and every one of them is an s-expression in brackets, never a "
       "sentence of English."))

(def system-prompt
  "The instruction half — static, because everything KB-specific rides in the user turn
  where the selection is.  It is deliberately short: the window belongs to the reader's
  content, not to a manual, and the deterministic critic
  (`vaelii.impl.llm.session/check-batch`) catches what the prose does not.

  The output contract is the **editor's line format**, so what the model writes is
  exactly what the textarea already holds and the round trip is the identity."
  (str
   "You edit a knowledge base of *sentexes*. A sentex is one sentence — a Lisp "
   "s-expression — plus the one context it holds in.\n\n"
   "You are given the lines the reader selected, a card describing only the vocabulary "
   "those lines use, and an instruction. Return the **complete edited set of lines**, "
   "one per line, and nothing else:\n\n"
   "    [<sentence> <Context>]\n"
   "    [<sentence> <Context> {:strength :monotonic}]\n\n"
   "- Keep a line you are not changing, **character for character**. Dropping a line "
   "deletes that sentex.\n"
   "- Change a line by returning it rewritten.\n"
   "- Add a line by returning one that was not in the selection.\n"
   "- Copy `{:strength :monotonic}` through unchanged; it means known-true, and losing "
   "it makes the fact defeasible.\n"
   "- Write no prose, no numbering, no markdown fence. Every line starts with `[` and "
   "ends with `]`.\n\n"
   "Naming is mechanical and enforced:\n\n"
   "| role | form | example |\n"
   "|---|---|---|\n"
   "| predicate | camelCase | `parentOf`, `ownedBy` |\n"
   "| individual | CapitalCamelCase | `Muffet`, `Ann` |\n"
   "| type | snake_case, used as a **unary** predicate | `dog`, `physical_object` |\n"
   "| context | CapitalCamelCase ending in `Context` | `WellContext` |\n\n"
   "Write `(dog Muffet)`, never `(isa Muffet Dog)`. A fact must be ground — no `?x` "
   "variables outside a rule. Reuse the vocabulary on the card rather than inventing a "
   "synonym for it, and prefer the most specific predicate the card offers.\n\n"
   worked-example))

(defn user-turn
  "The volatile half: the selected lines, the vocabulary card computed from them, and
  the reader's instruction — in that order, instruction last so it is the newest thing
  in the window."
  ([kb rows instruction] (user-turn kb rows instruction {}))
  ([kb rows instruction opts]
   (str "## Selected lines (" (count rows) ")\n\n"
        (str/join "\n" (map :line rows))
        "\n\n## Vocabulary used by these lines\n\n"
        (vocabulary-card kb rows opts)
        "\n\n## Instruction\n\n"
        (str/trim (str instruction)))))

;; ---- the context budget -------------------------------------------------

(def chars-per-token
  "Characters per token, for sizing a prompt before sending it.  Deliberately low —
  measured English-plus-s-expressions runs near 4, so 3.5 **over**-estimates, and an
  over-estimate refuses a selection that would have just fit rather than letting one
  that does not fit be silently truncated."
  3.5)

(defn estimate-tokens
  "A conservative token count for a string.  An estimate is what there is: Ollama
  exposes no tokenizer endpoint, and the exact count only comes back on the response
  as `prompt_eval_count` — which is the number to check an estimate against, and the
  reason `propose-edit` reports both."
  [s]
  (long (Math/ceil (/ (count (str s)) chars-per-token))))

(defn reserved-output-tokens
  "The output room a selection needs: one line back per line in, with slack for the
  lines it invents and for prose it was told not to write.  Reserved out of the window,
  because a prompt that fits with no room to answer is a prompt that does not fit."
  [n-lines]
  (+ 256 (* 48 (long n-lines))))

(defn budget
  "What a request of this shape costs against a window, as
  `{:prompt :reserved :total :num-ctx :headroom}` — all in estimated tokens."
  [system user n-lines num-ctx]
  (let [prompt   (+ (estimate-tokens system) (estimate-tokens user) 32)
        reserved (reserved-output-tokens n-lines)]
    {:prompt prompt
     :reserved reserved
     :total (+ prompt reserved)
     :num-ctx num-ctx
     :headroom (- num-ctx prompt reserved)}))

(defn budget-problem
  "The message explaining why this request does not fit `num-ctx`, or nil when it does.

  **A selection that does not fit is refused, never trimmed.**  Ollama silently drops
  the front of an over-long prompt, so a truncating request would answer about part of
  the reader's selection while appearing to answer about all of it — the one failure
  mode a reviewer cannot see."
  [{:keys [prompt reserved total num-ctx headroom]} n-lines]
  (when (neg? headroom)
    (str "the selection does not fit the model's context window: "
         n-lines " sentexes need about " total " tokens (" prompt " of prompt plus "
         reserved " reserved for the answer) against a window of " num-ctx
         ". Select fewer sentexes, or raise :num-ctx.")))
