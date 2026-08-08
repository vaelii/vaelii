;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.prompt
  "The system prompt, **generated from the live KB**.

  A hand-written copy of the ontology in a prompt string rots the moment someone
  drops a new `<Context>.txt` into `resources/kb/`.  So every section here is read
  back out of the KB it is about: the context topology from `contexts` /
  `context-up`, the type hierarchy from `types` / `genls`, the predicate
  documentation from the `(comment <term> \"…\")` sentexes the vocabulary documents
  itself with (`vaelii.impl.core-context/comment-of`), the argument types from the stored
  `argIsa` sentexes, the disjointness from `disjoint` / `disjointMetatype`, and the
  algebraic metadata from `props`.  The naming invariants are the one static section,
  because they are mechanical rules rather than content.

  The result is a **large stable prefix**: byte-identical across turns for an
  unchanged KB (every section is sorted, nothing carries a clock or an id), which is
  what prompt caching needs.  The volatile part — the user's request — lives in the
  message turn after the cache breakpoint, never in here."
  (:require [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]))

(def ^:private naming-rules
  "| role | convention | example |
|------|-----------|---------|
| predicate | camelCase, lowercase-initial | `parentOf`, `genl`, `argIsa` |
| individual | CapitalCamelCase | `Muffet`, `Tom` |
| type | snake_case, a **unary** predicate | `dog`, `physical_object` |
| context | CapitalCamelCase ending in `Context` | `WellContext`, `CoreContext` |

Types are unary predicates: write `(dog Muffet)`, never `(isa Muffet Dog)`. `thing` is the
root of the type hierarchy. A fact must be **ground** — `(mortal ?x)` asserts nothing
and is refused; a universal claim is written as a rule.")

(def ^:private output-contract
  "## What you produce

You do not write to the knowledge base. You **propose** an edit batch, which a human
reviews and applies. Your final message must contain exactly one fenced `edn` block
holding a map of this shape:

```edn
{:add    [[(dog Muffet) WellContext]
          [(parentOf Tom Ann) WellContext {:strength :monotonic}]]
 :remove [4211]}
```

- `:add` is a vector of `[sentence context]` or `[sentence context opts]`. The
  sentence is a plain s-expression; the context is a bare context symbol; `opts` is
  optional and carries `:strength :monotonic` for content known to be true (the
  default, `:default`, is defeasible).
- `:remove` is a vector of integer sentex handles. Look a handle up with
  `kb_handle_of` or `kb_sentexes_matching` before proposing its removal — never guess one.
- Either key may be omitted or empty. An empty batch is a valid answer when the
  request needs no change.

Write the batch **last**, after any prose. Put nothing else in the `edn` block.")

(def ^:private working-rules
  "## How to work

1. **Look before you write.** Use the read tools to check whether a term already
   exists (`kb_find_terms`), what a predicate's arguments must be (`kb_sentexes_matching` on
   `(argIsa ?p ?n ?t)`), what an individual already is (`kb_types_of`), and whether
   two types are disjoint (`kb_disjoint_p`). Reuse existing vocabulary rather than
   inventing a synonym.
2. **Assert facts, not universals.** Every `:add` sentence must be ground. Write a
   universal as a rule: `(implies (and (dog ?x)) (animal ?x))`, or wrap it in
   `(set/forwardRule …)` / `(set/backwardRule …)` to fix its direction, or
   `(set/defaultRule …)` to make it defeasible.
3. **Pick the most specific context that sees everything you need.** A context sees
   its `genlContext` ancestors; content asserted low is invisible from above.
4. **Say what you are unsure of** in prose above the batch. A batch is a proposal, so
   an uncertain entry costs a reviewer's attention, not a corrupted KB.")

;; ---- KB-derived sections ------------------------------------------------

(defn- bullet [& parts] (str "- " (str/join "" parts)))

(defn- context-section [kb {:keys [max-contexts] :or {max-contexts 40}}]
  (let [cs (sort (v/contexts kb))]
    (str "## Contexts (" (count cs) ")\n\n"
         "A sentex holds in exactly one context, and a context sees everything its\n"
         "`genlContext` ancestors hold. Listed with what each one sees:\n\n"
         (str/join "\n"
                   (for [c (take max-contexts cs)]
                     (let [up (sort (disj (set (v/context-up kb c)) c))]
                       (bullet "`" c "`"
                               (when (seq up)
                                 (str " — sees " (str/join ", " (map #(str "`" % "`") up))))))))
         (when (> (count cs) max-contexts)
           (str "\n- … and " (- (count cs) max-contexts) " more (`kb_contexts`)")))))

(defn- type-section [kb {:keys [max-types] :or {max-types 80}}]
  (let [ts (sort (v/types kb))]
    (str "## Types (" (count ts) ")\n\n"
         "Each is a unary predicate; `genls` are its supertypes.\n\n"
         (str/join "\n"
                   (for [t (take max-types ts)]
                     (let [up (sort (disj (set (v/genls kb t)) t))]
                       (bullet "`" t "`"
                               (when (seq up)
                                 (str " ⊂ " (str/join ", " (map #(str "`" % "`") up))))))))
         (when (> (count ts) max-types)
           (str "\n- … and " (- (count ts) max-types) " more (`kb_types`)")))))

(defn- argisa-index
  "predicate -> sorted [[position type] …], from the stored `argIsa` sentexes."
  [kb]
  (reduce (fn [m {:keys [sentence]}]
            (let [[_ pred n t] sentence]
              (update m pred (fnil conj []) [n t])))
          {}
          (v/sentexes-matching kb (list 'argIsa '?p '?n '?t) '?ctx)))

(defn- predicate-section [kb {:keys [max-predicates] :or {max-predicates 60}}]
  (let [argisa (argisa-index kb)
        preds  (sort (set (concat (keys argisa)
                                  (filter #(= :predicate (v/term-role %)) (v/terms kb)))))
        shown  (take max-predicates preds)]
    (str "## Predicates (" (count preds) ")\n\n"
         "`argIsa` gives the type each argument position must satisfy — an argument\n"
         "carrying a type that cannot reach it is refused.\n\n"
         (str/join "\n"
                   (for [p shown]
                     (let [doc  (first (core-context/comment-of kb p))
                           args (sort-by first (get argisa p))]
                       (bullet "`" p "`"
                               (when (seq args)
                                 (str " — args: "
                                      (str/join ", " (for [[n t] args] (str n ":`" t "`")))))
                               (when doc (str " — " (str/replace doc #"\s+" " ")))))))
         (when (> (count preds) max-predicates)
           (str "\n- … and " (- (count preds) max-predicates) " more (`kb_find_terms`)")))))

(defn- metadata-section [kb]
  (let [kinds [:transitive :symmetric :reflexive :functional :universal]
        rows  (for [k kinds
                    :let [ps (sort (v/props kb k))]
                    :when (seq ps)]
                (bullet "**" (name k) "** — " (str/join ", " (map #(str "`" % "`") ps))))
        invs  (sort (set (for [p (sort (v/terms kb))
                               :let [q (v/inverse-of kb p)]
                               :when q]
                           (vec (sort [p q])))))]
    (when (or (seq rows) (seq invs))
      (str "## Predicate metadata\n\n"
           (str/join "\n" rows)
           (when (seq invs)
             (str (when (seq rows) "\n")
                  (bullet "**inverse** — "
                          (str/join ", " (for [[a b] invs] (str "`" a "`/`" b "`"))))))))))

(defn- disjoint-section [kb]
  (let [pairs (sort (set (for [{:keys [sentence]} (v/sentexes-matching kb (list 'disjoint '?a '?b) '?ctx)]
                           (vec (sort [(nth sentence 1) (nth sentence 2)])))))
        metas (sort (v/disjoint-metatypes kb))]
    (when (or (seq pairs) (seq metas))
      (str "## Disjointness\n\n"
           "Disjoint types share no instance. Asserting a type membership that clashes\n"
           "with one an individual already holds is refused.\n\n"
           (str/join "\n"
                     (concat
                      (for [[a b] pairs] (bullet "`" a "` / `" b "`"))
                      (for [m metas]
                        (bullet "metatype `" m "` — pairwise disjoint members: "
                                (str/join ", " (map #(str "`" % "`")
                                                    (sort (v/metatype-members kb m))))))))))))

(defn- scale-section [kb]
  (str "## This knowledge base\n\n"
       (bullet (v/term-count kb) " distinct terms across " (count (v/contexts kb)) " contexts.\n")
       (bullet "Use the read tools to explore it; nothing below is the whole picture.")))

;; ---- the assembled prompt -----------------------------------------------

(defn system-prompt
  "The generated system prompt for `kb`, as one string.

  `opts` bounds the enumerated sections so a large KB does not push the whole
  vocabulary into every request: `:max-contexts` (40), `:max-types` (80),
  `:max-predicates` (60).  `:preamble` prepends application-specific instruction ahead
  of everything else.

  Deterministic for a given KB and opts — sorted throughout, no clock, no handles — so
  it is a stable cache prefix."
  ([kb] (system-prompt kb {}))
  ([kb opts]
   (->> [(:preamble opts)
         (str "You are a knowledge engineer working on **vaelii**, a contextualized "
              "common-sense knowledge base. The unit of knowledge is a *sentex*: a "
              "sentence (an s-expression) plus the one context it holds in. Your job is "
              "to read the existing knowledge with the tools you are given and propose "
              "well-formed additions and removals.")
         output-contract
         working-rules
         (str "## Naming invariants\n\n" naming-rules)
         (scale-section kb)
         (context-section kb opts)
         (type-section kb opts)
         (predicate-section kb opts)
         (metadata-section kb)
         (disjoint-section kb)]
        (remove str/blank?)
        (str/join "\n\n"))))
