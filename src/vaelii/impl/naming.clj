;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.naming
  "KB naming invariants, as predicates over symbols — and the walk that applies them to
  every **literal** of a sentence rather than to its outermost functor alone.

    predicate    camelCase, lowercase-initial, arity 2+         parentOf, genlCx, arg
    individual   CapitalCamelCase                               Muffet, Tom
    type         snake_case, lowercase, unary predicate         dog, physical_object
    sense        a type, plus which sense of it is meant        abrasive-grit
    context      Cx prefix, then CapitalCamelCase               CxUniverse, CxCore
    lexeme       the `lex` namespace; the name is parse input   lex/fool's_gold

  Single lowercase words (dog, genl, parentOf) satisfy both `predicate?` and
  `type-symbol?`; role is disambiguated by position and arity, not the symbol alone.
  A sense is a type too, so it is unary for the same reason, and a lexeme is the one
  role a *namespace* decides — its text is a surface form and not ours to spell.
The spelling is a **biconditional on arity**.  A functor carrying an underscore is a
  type name and nothing else, and types are used as *unary* predicates — `(dog Muffet)`,
  not `(isa Muffet Dog)` — so it is legal at arity 1 and nowhere else.  And the converse
  now holds too: a *camelCase* functor at arity 1 is refused, because a one-place
  predicate is a kind or a property rather than a relation between terms, and the whole
  point of a spelling that reads a role is that it reads it in both directions.
  `(lives_in penguin cold_place)` is a type name doing a relation's job;
  `(warmBlooded Muffet)` is a property wearing a relation's spelling.  A bare lowercase
  word (`dog`, `alive`) satisfies both conventions and is caught by neither, which is
  where the rule stops: it marks the names that carry more than one word.

  How hard these are enforced is the **KB's** to say, not this namespace's: `open-kb`'s
  `:naming` selects `:strict` / `:warn` / `:off` (`policies`, below) and `assert` reads
  it.  The predicates themselves do not move — `:off` stores a name nothing can classify,
  not one classified differently.

  `problems` checks the functor of every literal a sentence contains — a rule's
  antecedents, its consequent, an `exceptWhen` query's conjuncts, a `not` body, an
  `ist`-directed sentence, a negation-as-failure query — not only the outermost one.
  A rule consequent is exactly where generated content lands, and the outermost
  functor there is `implies`."
  (:refer-clojure :exclude [name])
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.sentex :as sx])
  (:import (clojure.lang ExceptionInfo)))

(defn- nm [s] (clojure.core/name s))

(def lexeme-namespace
  "The namespace marking a **lexeme** — a surface form exactly as a model or a person
  wrote it, before anything decided what it means.  A namespace rather than a spelling
  because a lexeme's own text is unconstrained: it carries apostrophes (`fool's_gold`),
  dashes, dots and digits, so any marker written *into* the name would collide with the
  word it marks.  `(namespace x)` is a field read and cannot."
  "lex")

(defn lexeme?
  "A lexeme: `lex/fool's_gold`.  Parse input, and the only role whose text this makes no
  claim about — what a person typed is not ours to spell.

  Every other namespace stays invisible to the role checks: `nm` reads the name half, so
  `agg/count` and `set/forwardRule` are read as the predicates `count` and `forwardRule`.
  `lex` is the one namespace that decides a role."
  [x]
  (and (symbol? x) (= lexeme-namespace (namespace x))))

(def context-namespace
  "Reserved namespace of a reified **context** constant (`vaelii.impl.nat`,
  docs/context-nat.md) — a `cx/` symbol is a context by the same spelling-only rule as a
  `Cx…` name.  Duplicated here as a literal rather than required from `vaelii.impl.nat`
  (which requires *this* namespace) so the role predicates stay dependency-free."
  "cx")

(defn context?
  "A context: a `Cx…` CapitalCamelCase name, or a reified context constant in the `cx/`
  namespace.  Both decided by spelling alone — role-reading never consults belief
  (docs/naming.md), which is why a reified *context* NAT carries its own namespace rather
  than a `(context K)` mark a `context?` would have to look up."
  [x]
  (and (symbol? x) (not (lexeme? x))
       (or (= context-namespace (namespace x))
           (some? (re-matches #"Cx[A-Z][A-Za-z0-9]*" (nm x))))))

(def query-contexts
  "The **query contexts**: three `Cx…` symbols naming a *reading mode* rather than a
  place.

  Cyc reifies `InferencePSC` / `EverythingPSC` as contexts you can assert into.
  Here scope is a property of the read (docs/from-cyc.md), so these are resolved at the
  read entry point and **never reach the engine** — nothing is stored in one, no `genlCx` edge
  names one, and `core/contexts` does not list them.  Each names one of the readings the
  engine already had and could not spell:

  | symbol | belief | whose view must hold the answer |
  |---|---|---|
  | `CxEverything` | **ignored** | — (not a view question at all) |
  | `CxInference` | followed | every literal in **one** view, handed back as `?ctx` |
  | `CxNothing` | followed (vacuously) | the empty view: the provers alone |

  A **variable** context (`?ctx`, the default of every short arity) is the fourth spelling
  of the `CxInference` question.  It follows belief like the last two and reads **joint**
  like `CxInference`: an answer holds only from some one reader's `genlCx` ancestor set, so two
  facts no single context sees are never joined — and that reader unifies into the
  variable, where `CxInference` hands it back as `?ctx` beside the bindings
  (docs/contexts.md).

  These are **two axes and not a ladder**.  `CxEverything` alone stops following belief,
  which makes it a different kind of question — its answers are not belief claims — while
  `?ctx`, `CxInference` and an ordinary context all ask what the KB holds and differ only in
  whose view has to hold it.  A reader who takes the roster for an ordered list concludes
  that `?ctx` is a near neighbour of `CxEverything`, and it is not.

  Spelled `Cx…` because they stand where a context stands, and deliberately left **in**
  `context?`, which is spelling alone and stays that way: a role-read asking what a symbol
  looks like must not have to know this roster.  What refuses them is the write side,
  where the difference between a place and a reading is an invariant rather than a naming
  policy — `core/assert`'s context slot, and the `genlCx` argument slots at
  `vaelii.impl.wff`."
  '#{CxEverything CxInference CxNothing})

(defn query-context?
  "Is `x` a query context — a reading mode wearing a context's spelling?  See
  `query-contexts` for the roster and what each one reads."
  [x]
  (contains? query-contexts x))

(defn individual? [x] (and (symbol? x) (not (lexeme? x))
                           (some? (re-matches #"[A-Z][A-Za-z0-9]*" (nm x)))
                           (not (context? x))))
(defn predicate?  [x] (and (symbol? x) (not (lexeme? x))
                           (some? (re-matches #"[a-z][a-zA-Z0-9]*" (nm x)))))

(def ^:private disambiguator-re
  "A **sense** — a word, a `-`, and the disambiguator that says which sense of it is
  meant: `abrasive-grit`, `abandonment-romantic`, `abandonment-dual`.  Senses are the
  type hierarchy, and the disambiguator is what makes two senses of one word two terms
  rather than one.

  The split is on the **last** dash, because the word may hold its own — and may *end*
  in one, which is the case that forces the rule.  `a-` is a word (A, then the minus),
  so its sense is `a--musical_note`: the word is `a-`, the disambiguator is
  `musical_note`, and the boundary is the second dash rather than the first.  Nothing
  here parses that boundary — the `sense` and `disambiguation` facts record it, and this
  only has to recognise the shape.

  Both halves admit what real vocabulary carries — a leading dot (`.22_long_rifle-ammo`,
  `.dll-library`), an internal apostrophe (`fool's_gold-mineral`, `deck-ship's_floor`), a
  dash of the word's own, and a disambiguator that starts with a digit (`organ_cultures-3d`,
  `chiptune_composer-8bit`).  A disambiguator is minted rather than found, so it is
  tempting to hold it to snake_case — but the corpus mints `3d` and `8bit`, and they are
  good disambiguators.  Only the **first character of the whole symbol** is constrained,
  because only it is what the reader dispatches on.

  What it may not do is **lead with a digit**, and the reason is the reader rather than
  taste: `134a-gas` is read as a malformed *number*, not as a symbol, so a KB holding one
  could not be written to text and read back.  A leading `'`, `#` or `:` fails the same
  way.  A word that starts with a digit is escaped with an underscore when it is minted
  — `_134a-gas` — which reads, sorts beside its neighbours, and says it was escaped."
  #"[a-z._][a-z0-9_'.+=&:*>#-]*-[a-z0-9][a-z0-9_']*")

(defn sense?
  "A disambiguated type."
  [x]
  (and (symbol? x) (not (lexeme? x))
       (some? (re-matches disambiguator-re (nm x)))))

(defn type-symbol?
  "A type: bare snake_case (`dog`, `physical_object`) or a sense (`abrasive-grit`).
  Both are unary predicates — a sense is a type that says which sense it is."
  [x]
  (and (symbol? x) (not (lexeme? x))
       (or (some? (re-matches #"[a-z][a-z0-9_]*" (nm x)))
           (sense? x))))

(defn functor [sentence] (when (sequential? sentence) (first sentence)))
(defn args    [sentence] (when (sequential? sentence) (rest sentence)))
(defn arity   [sentence] (if (sequential? sentence) (dec (count sentence)) 0))

;; ---- a structural order on sentence / context content --------------------
;; Clash reports and `(contradicts …)` sentences are read in a stable, arrival-free
;; order, and the tempting way to buy one is a `pr-str` key: cheap, and a string's
;; lexicographic order is total.  It has two costs the engine was already bitten by
;; (`kb/antecedent-order`, `solve/content-key`, `settle/content-order`).  It allocates
;; a String per element per comparison — the keyfn runs inside the comparator, so a
;; sort builds it ~2·n·log₂n times.  And an ambient `*print-length*` / `*print-level*`
;; — a REPL's, typically — elides two long sentences to one prefix, collapsing the key
;; and dropping the tie back onto arrival order, the very dependence a content order
;; exists to remove.  Those sites bind the print vars off; `compare-form` never prints.

(defn print-key
  "`x` printed as a content key: `pr-str` with the print bounds released.

  **The one home for a printed ordering key.**  `compare-form` is the cheaper answer
  and the one to reach for first, but a few keys are printed on purpose — a
  `Comparable` String whose lexicographic order is the contract, or a tuple mixing a
  form with a rank.  Every one of them owes this guard, and the reason is the paragraph
  above: an ambient `*print-length*` / `*print-level*` — a REPL's, typically — elides two
  long sentences to one prefix, the key collapses, and the tie falls back to the
  enumeration order the content key exists to keep out.  A short sentence is not safe
  either: `*print-length*` 3 prints `(arg parentOf 1 person)` and `(arg parentOf 1 animal)`
  as the same string.

  `*print-meta*` is bound off with them, so a form carrying metadata keys the same as one
  that does not — the metadata is no part of what a sentence says.

  One binding frame per call, which is why a caller ordering a large collection binds
  once around the whole sort instead and prints inside it.  `sort_by_content_key_test`
  scans the sources for a printed key that reaches neither this fn nor such a frame."
  ^String [x]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (pr-str x)))

(defn- form-rank
  "A total order on the *kinds* of thing a sentence is built from, so `compare-form`
  never throws on a mixed pair — which `clojure.core/compare` does across types — and
  orders them deterministically instead.  A sentence is EDN: symbols (predicates,
  terms, contexts, `?vars`), numbers, strings, keywords, booleans, and the one nested
  kind a value or a term is — a sequential."
  [x]
  (cond
    (nil? x)        0
    (boolean? x)    1
    (number? x)     2
    (char? x)       3
    (string? x)     4
    (keyword? x)    5
    (symbol? x)     6
    (sequential? x) 7
    :else           8))

(defn compare-form
  "A structural total order on sentence / context content — what a clash report's sides
  and a `(contradicts …)` sentence are ordered by — computed by walking the two forms
  in place rather than printing them.  A drop-in `Comparator` for `sort` / `sort-by`.

  Total and deterministic, and read from **content alone**: no handle enters it, so a
  tie it breaks is broken the same way in every arrival order.  Different kinds order by
  `form-rank`; same-kind scalars by the natural `compare` (symbols by ns then name,
  numbers numerically, and so on); two sequentials element by element, then shorter
  first — so `(a)` precedes `(a b)`.  The last-resort `:else` is unreachable for
  well-formed sentence content and totalizes the order for an exotic value alone — a map,
  a set, a record.  It prints through `print-key` rather than `str`, so it totalizes
  *honestly*: `str` on a collection honours the ambient print bounds, and two distinct
  maps compared under a REPL's `*print-length*` come back **equal** — a comparator that
  reports 0 for values that are not, in the one branch whose whole job is to leave no
  pair uncompared.  One binding frame per comparison is what that costs, on the branch
  sentence content never reaches.

  The order is arbitrary but stable, which is the contract a content order owes
  (docs/nmtms.md).  It is deliberately **not** the lexicographic order `pr-str` gave —
  `(a)` before `(a b)` where the printed forms compared the other way — so a caller that
  had pinned that exact reading re-pins this one."
  [a b]
  (let [ra (form-rank a) rb (form-rank b)]
    (cond
      (not= ra rb) (compare ra rb)
      (= 7 ra)     (loop [xs (seq a) ys (seq b)]
                     (cond
                       (and (nil? xs) (nil? ys)) 0
                       (nil? xs)                 -1
                       (nil? ys)                  1
                       :else (let [c (compare-form (first xs) (first ys))]
                               (if (zero? c) (recur (next xs) (next ys)) c))))
      (= 0 ra)     0
      (= 8 ra)     (compare (print-key a) (print-key b))
      :else        (compare a b))))

(defn name-key
  "`x` as an ordering key where the value is a **scalar** — a symbol, keyword, string or
  number.  `str` on one of those cannot collapse: the print bounds elide a *collection*
  and never a name, so a scalar key is safe as it stands and this is `str`.

  What it adds is that the scalar is a claim rather than an assumption.  `str` honours
  the print vars exactly as `pr-str` does, so a key that turns out to be a sentence, a
  NAT or a binding map collapses under a REPL's `*print-length*` and the tie it was
  breaking falls back to arrival order — silently, since both readings are legal strings.
  A collection reaching here is handed to `print-key` instead, which is the guarded
  answer for one, so a NAT arriving where a symbol was expected is keyed safely rather
  than wrongly.

  Cheap where `print-key` is not: no binding frame, no printer, so a plain `sort-by` over
  scalars needs no decorating.  `compare-form` is still the first thing to reach for
  where the order may be structural; these two are for a key that must be a `Comparable`
  String."
  ^String [x]
  (if (coll? x) (print-key x) (str x)))

(defn sort-by-content-key
  "`coll` ordered by `(keyfn element)` under `cmp` — the decorate-sort-undecorate the
  engine's content orders share, in one place.  It closes at once the three costs the
  scattered `sort-by <expensive-key>` sites each paid:

  * **The key is built once per element, not once per comparison.**  `sort-by` calls its
    key fn from inside the comparator, so a plain `(sort-by keyfn coll)` rebuilds the key
    ~2·n·log₂n times; here one `mapv` decorates each element with its key, the pairs sort
    on the key alone, and the key is stripped.  When the key is a `get-sentex` per
    antecedent, a `pr-str`, or a taxonomy-closure read, that is the difference between n
    builds and n·log n.
  * **Below two there is nothing to order** — a collection of zero or one is already in
    its own order and the key is what orders, so no key is built at all.  This is the
    shape `supporting-justifications` on a one-justification fact meets on every proof hop.
  * **`cmp` defaults to `compare-form`** — structural, so no String is printed to compare
    two forms.  Pass `compare` when the key is a pre-built `Comparable` tuple (a
    `[rank …]` priority vector, or a `print-key` whose lexicographic order is the
    contract).  This does **not** bind the print vars for you: a printed key is built by
    the caller's `keyfn`, so `print-key` is where that guard lives.

  Stable: `sort-by` keeps equal-keyed elements in `coll`'s order, so a tie falls to
  arrival only after the content key has had its say — never onto a handle."
  ([keyfn coll] (sort-by-content-key keyfn compare-form coll))
  ([keyfn cmp coll]
   (let [v (vec coll)]
     (if (< (count v) 2)
       v
       (->> v (mapv (fn [x] [(keyfn x) x])) (sort-by first cmp) (mapv second))))))

(defn min-by-content-key
  "The `sort-by-content-key`-least element of `coll` — `(first (sort-by-content-key keyfn cmp coll))`
  in a single pass, building the key once per element where the sort would build it once
  and then discard all but the first.  Ties keep the earliest arrival, exactly as the
  stable sort's `first` would.  nil for an empty `coll`.  `cmp` defaults to `compare-form`."
  ([keyfn coll] (min-by-content-key keyfn compare-form coll))
  ([keyfn cmp coll]
   (when-let [s (seq coll)]
     (second
      (reduce (fn [a b] (if (neg? (long (cmp (first b) (first a)))) b a))
              (map (fn [x] [(keyfn x) x]) s))))))

(defn by-print-key
  "`coll` ordered by its elements' `print-key` — the guarded form of `(sort-by str coll)`,
  and what a caller ordering terms, sentences or pairs wants when the printed order is
  the contract.

  `sort-by-content-key` underneath, so the key is built **once per element** rather than
  once per comparison, which is what a printed key costs most in: `sort-by` calls its key
  fn from inside the comparator, and `print-key` opens a binding frame per call.  `compare`
  because a printed key's lexicographic order is the whole reason it was printed."
  [coll]
  (sort-by-content-key print-key compare coll))

;; ---- the literals of a sentence ------------------------------------------
;; A naming invariant is about a **literal** — a predicate applied to arguments.
;; Everything else a sentence is built from is a *wrapper*: a structural connective
;; (`not` / `and` / `implies`), a virtual rule wrapper (`set/*Rule`), an `exceptWhen`,
;; an `ist` redirection, a negation-as-failure quantifier, a `sentexHandle` naming
;; another sentex.  A wrapper's functor is engine vocabulary rather than a name the
;; author chose, so the walk descends through it and checks what it holds.
;;
;; Arguments are deliberately **not** walked: a compound in argument position is a
;; term, not a literal — an arithmetic expression `(+ 1 2)`, a structural NAT `(QuantityFn 5
;; Meter)`, a quoted connective `(comment not "…")` — and its head names a function or
;; is plain data, neither of which the predicate conventions govern.

(def ^:private literal-roles
  "The wrapper a literal sits in, as it reads in a rejection.  A repair loop is handed
  the message verbatim, so it has to say *which* literal of the sentence broke."
  {:sentence   "sentence"
   :antecedent "rule antecedent"
   :consequent "rule consequent"
   :exception  "exceptWhen exception"
   ;; a generator's stamped rule (docs/generators.md) — named apart from the
   ;; generator's own literals, because an author reading the rejection has two rules
   ;; in one sentence to tell apart
   :generated-antecedent "generated rule antecedent"
   :generated-consequent "generated rule consequent"})

(def problem-classes
  "What a naming violation *is*, as a keyword, with the human line under it.  A rejection
  reads as prose, but a caller that counts them needs to group without parsing English —
  an operator auditing a corpus wants seven numbers, not eleven million sentences — so the
  class is the datum and the message is rendered from it."
  {:context-name   "the KB context named is not a context"
   :functor        "a functor matching no convention"
   :functor-arity  "a snake_case functor (a unary predicate) at an arity other than 1"
   :functor-unary  "a camelCase functor at arity 1 — a unary predicate is snake_case"
   :lexeme-functor "a lexeme applied to arguments — a surface form names no relation"
   :argument       "a symbol argument matching no convention"
   :ist-context    "an ist context slot that does not name a context"
   :dot-marker     "a dotted rest marker outside a rule pattern"})

(defn- rule-wrapper?
  "One of the virtual wrappers that wrap a single rule form — direction, defeasible,
  assumption, constraint.  Each canonicalizes into a record field, so none of them is
  ever a predicate application."
  [h]
  (or (contains? sx/rule-direction-wrappers h)
      (= sx/default-rule-wrapper h)
      (= sx/assumption-rule-wrapper h)
      (contains? sx/constraint-rule-wrappers h)))

(defn- exception-query-conjuncts
  "The conjunct literals of an `exceptWhen` wrapper's query: a vector is a conjunction,
  anything else a single literal.  The shape `sentex/exception-conjuncts` normalizes,
  read here without canonicalizing — a check must not intern the symbols of content it
  is about to refuse."
  [q]
  (if (vector? q) q [q]))

(defn applied-literals
  "The `[role literal]` pairs of `sentence` as written — every position at which it
  applies *something* to arguments, tagged with the wrapper that position sits in
  (`:sentence` / `:antecedent` / `:consequent` / `:exception`).

  Wrappers are descended through, arguments are not, so this is exactly the set of
  positions an author wrote a predicate application in — a variable functor
  (`(?p ?x ?y)`, the dotted rest `(?pred . ?args)`) among them, which is what
  `literals` filters back out and `rules/variable-functor-literals` keeps."
  ([sentence] (applied-literals :sentence sentence))
  ([role form]
   (if-not (and (sequential? form) (seq form))
     []
     (let [h (first form)
           n (count form)]
       (cond
         ;; a `do/` imperative is an instruction; it is refused outright inside a rule
         ;; (`core/check-no-imperative`) and dispatched at the top level, never named
         (sx/do-form? form) []

         ;; `(sentexHandle N)` names a stored sentex by integer id
         (= sx/sentex-handle-functor h) []

         (sx/variable? h) [[role form]]

         (rule-wrapper? h) (applied-literals role (second form))

         ;; `(exceptWhen <query> <rule-or-handle>)` — the query's conjuncts are
         ;; literals of their own, then whatever the exception qualifies
         (and (= sx/except-wrapper h) (= 3 n))
         (into (vec (mapcat #(applied-literals :exception %)
                            (exception-query-conjuncts (second form))))
               (applied-literals role (nth form 2)))

         (and (= sx/not-functor h) (= 2 n)) (applied-literals role (second form))

         (= sx/and-functor h) (vec (mapcat #(applied-literals role %) (rest form)))

         ;; A rule in **consequent** position is a generator's stamped rule
         ;; (docs/generators.md), and its literals are tagged as such: the naming
         ;; invariants hold of them exactly as they hold of a written rule's — a
         ;; stamped `(feels ?a ?e)` is still a predicate application — but the
         ;; *index* has no claim on them, because what gets indexed is the mint and
         ;; not the pattern.  `rules/variable-functor-literals` reads the tag to draw
         ;; that line, which is what lets a hole stand in functor position.
         ;;
         ;; A stamped rule may stamp one in turn, so a *stamped* consequent is a
         ;; generator's head by the same reading: the tag survives the whole nesting,
         ;; and a literal three levels in still reads as stamped rather than as the
         ;; author's own.
         (and (= sx/rule-functor h) (= 3 n))
         (let [gen?  (contains? #{:consequent :generated-consequent} role)
               arole (if gen? :generated-antecedent :antecedent)
               crole (if gen? :generated-consequent :consequent)]
           (into (vec (mapcat #(applied-literals arole %) (sx/rule-antecedents form)))
                 (applied-literals crole (sx/rule-consequent form))))

         ;; `(ist Ctx S)` directs S into Ctx; S is the literal (Ctx is checked by
         ;; `ist-context-problems`)
         (and (= sx/ist-functor h) (= 3 n)) (applied-literals role (nth form 2))

         ;; negation as failure: `(unknown S)` and `(thereExists <vars> S)` wrap a
         ;; query, and a head `(exists <vars> C)` wraps the consequent it quantifies
         (sx/unknown? form)      (applied-literals role (second form))
         (sx/there-exists? form) (applied-literals role (nth form 2))
         (sx/head-exists? form)  (applied-literals role (sx/head-exists-body form))

         ;; an aggregate wraps a query too: `(agg/count ?n ?v <body>)` says
         ;; nothing itself, and its body is a goal rather than an argument — read as a
         ;; literal it would be a three-place `agg/count` and the body inside it
         ;; would never be checked at all
         (sx/aggregate? form)    (applied-literals role (sx/aggregate-body form))

         :else [[role form]])))))

(defn literals
  "The `[role literal]` pairs whose functor **names a predicate** — `applied-literals`
  without the variable-functor positions, which are patterns and name nothing these
  invariants can judge.  This is the set of functors an author named, and what every
  check below reads."
  ([sentence] (literals :sentence sentence))
  ([role form]
   (filterv (fn [[_ lit]] (not (sx/variable? (first lit))))
            (applied-literals role form))))

;; ---- the invariants, per literal -----------------------------------------

(defn- camel-case
  "The camelCase spelling of a snake_case symbol — `lives_in` ⇒ `livesIn`.  Named in
  the rejection so whoever reads it is told what to write, not only what is wrong."
  [s]
  (let [[head & more] (str/split (nm s) #"_+")]
    (apply str head (map str/capitalize more))))

(def unary-spelling-exempt
  "The camelCase functors that stand at arity 1 and are **not** unary predicates, so the
  snake_case rule does not reach them.  `sentexHandle` names a stored sentex by its id —
  a term constructor wearing a literal's shape, which states nothing and so is no
  predicate to spell either way.  Kept as a roster rather than a shape test because it is
  engine vocabulary and finite; a name earns a place here only by naming no relation."
  '#{sentexHandle})

(defn snake-case
  "The snake_case spelling of a camelCase symbol — `warmBlooded` ⇒ `warm_blooded`.  The
  inverse of `camel-case`, and what a `:functor-unary` rejection proposes."
  [s]
  (symbol (str/replace (nm s) #"([A-Z])" (fn [[_ c]] (str "_" (str/lower-case c))))))

(defn- functor-problem
  "The naming violation of one `[role literal]` pair's functor, or nil.  Two ways to
  fail: the symbol matches no convention at all, or it is snake_case — a type name —
  used at an arity other than 1."
  [[role literal]]
  (let [f (functor literal)]
    (cond
      (nil? f) nil

      ;; The one fence around a lexeme, and the whole of it.  A surface form is what
      ;; somebody wrote, not a relation or a kind, so it cannot be applied to anything —
      ;; while as an *argument* it is ordinary, which is what lets `(sense lex/w s)` say
      ;; what a lexeme means and `(genl s lex/w)` stand as an unsensified edge until a
      ;; sense is crafted to replace it.
      (lexeme? f)
      {:class :lexeme-functor :role role :symbol f :literal literal}

      (not (or (predicate? f) (type-symbol? f)))
      {:class :functor :role role :symbol f :literal literal}

      (and (not (predicate? f)) (not= 1 (arity literal)))
      {:class :functor-arity :role role :symbol f :literal literal}

      ;; The converse fence, and what makes the spelling a biconditional: snake_case is
      ;; arity 1, and arity 1 is snake_case.  A camelCase functor carries an interior
      ;; capital, so `type-symbol?` refuses it, and applied to one argument it is a unary
      ;; predicate spelled as a relation.  A bare lowercase word satisfies both
      ;; conventions and is therefore never caught here — which is why `dog` and `alive`
      ;; need no underscore and never will.
      (and (not (type-symbol? f)) (= 1 (arity literal))
           (not (contains? unary-spelling-exempt f)))
      {:class :functor-unary :role role :symbol f :literal literal})))

(defn- pascal-case
  "The CapitalCamelCase spelling of an underscored symbol — `South_Pole` ⇒ `SouthPole`."
  [s]
  (apply str (map str/capitalize (str/split (nm s) #"_+"))))

(defn- argument-problem
  "The naming violation of one atomic symbol argument, or nil.  An argument *names*
  something — an individual, a type, a predicate, a context — so it is held to the
  same conventions as a functor.  `Baby_Penguin` matches none of them: CapitalCamelCase
  admits no underscore and snake_case no capital, so the symbol claims two roles and
  fills neither.  Both repairs are named, since which one is meant is the author's to
  say: `BabyPenguin` if it is an individual, `baby_penguin` if it is a type.

  Only the literal's **own** arguments are checked, never a compound one's insides: a
  compound in argument position is a term — `(+ 1 2)`, a structural NAT `(QuantityFn 5 Meter)` —
  and its head is a function, not a name this can judge.  Non-symbols (a number, a
  comment's string) name nothing and are skipped, as is a variable and the dotted rest
  marker."
  [[role literal] a]
  (when (and (symbol? a)
             (not (sx/variable? a))
             (not= sx/dot-marker a)
             (not (or (individual? a) (context? a) (predicate? a) (type-symbol? a)
                      (lexeme? a))))
    {:class :argument :role role :symbol a :literal literal}))

(defn- ist-context-problems
  "The `(ist Ctx S)` context slots that do not name a context.  `(ist Ctx S)` names the
  context S is asserted into or asked in, so that slot is a context name like the
  asserting context.  A variable in the slot is a pattern position and is not judged.

  `sx/forms-where` rather than a `tree-seq`, and this is the check that wants it: an
  `ist` can sit anywhere, so this is the only one here that descends **arguments** —
  every node of every sentence asserted, to find a form almost none of them hold.
  Depth-first pre-order either way, which is the order `problems` reports."
  [sentence]
  (mapv (fn [f] {:class :ist-context :role :sentence :symbol (second f) :literal f})
        (sx/forms-where #(and (sequential? %)
                              (= sx/ist-functor (first %))
                              (= 3 (count %))
                              (not (or (sx/variable? (second %)) (context? (second %)))))
                        sentence)))

(defn message
  "One `problems*` map rendered as the line a rejection carries.  Every message names
  the offending symbol, the wrapper it sits in and the spelling to write instead: whoever
  reads it is mid-repair, and a violation reported without its fix is a second lookup."
  [{:keys [class role symbol literal]}]
  (let [where (str (literal-roles role) " " (pr-str literal))]
    (case class
      :context-name
      (str "context " symbol " must start with Cx and continue CapitalCamelCase")

      :functor
      (str "functor " (pr-str symbol) " in " where " matches no naming convention: a"
           " predicate is camelCase (parentOf, arg), a type is snake_case"
           " (physical_object) or a sense (abrasive-grit), and a type is only unary")

      :lexeme-functor
      (str "functor " (pr-str symbol) " in " where " is a lexeme, and a surface form names"
           " no relation, so it cannot be applied to anything — write the sense it means,"
           " " (nm symbol) "-<which sense>, or leave it in argument position, where"
           " (sense " symbol " <the sense>) says what it means")

      :functor-arity
      (if (sense? symbol)
        (str "functor " symbol " in " where " is a sense, which names a type and is legal"
             " only as a unary predicate, but has " (arity literal) " arguments — write the"
             " relation as a camelCase predicate, or as (" symbol " <one argument>)")
        (str "functor " symbol " in " where " is snake_case, which names a unary"
             " predicate — a kind or a property — and is legal only at arity 1, but has "
             (arity literal) " arguments — write it camelCase as " (camel-case symbol)
             ", or as (" symbol " <one argument>)"))

      :functor-unary
      (str "functor " symbol " in " where " is camelCase and has one argument, but a"
           " unary predicate is snake_case — a one-place predicate is a kind or a"
           " property, not a relation between terms, and the spelling says so. Write it"
           " " (snake-case symbol) ", or give it the arguments a relation takes")

      :argument
      (str "argument " (pr-str symbol) " in " where
           " matches no naming convention: an individual is CapitalCamelCase (Muffet), a"
           " type is snake_case (physical_object) or a sense (abrasive-grit), and a"
           " predicate is camelCase (parentOf) — write it " (pascal-case symbol)
           " for an individual, or " (str/lower-case (nm symbol)) " for a type")

      :ist-context
      (str "ist directs " (pr-str literal) " into " (pr-str symbol)
           ", which must start with Cx and continue CapitalCamelCase")

      :dot-marker
      "'.' is not a valid argument (dotted rest patterns belong in rule patterns)")))

(defn problems*
  "Checkable naming violations for a sentence in a context, as **data**: a vector of
  `{:class :role :symbol :literal}` maps in the order `problems` reports them.  `:class`
  is one of `problem-classes`, `:role` the wrapper the offending literal sits in, `:symbol`
  the name that broke the convention, and `message` renders the line.

  Data rather than prose because the two callers want different halves of it.  `assert`
  wants the sentence it refused spelled out; an audit over a whole corpus wants to
  *group* — how many violations, of which class, over how many distinct spellings — and
  a message that embeds the literal is unique per record, so counting them counts
  records.  Rendering is therefore separate and paid only where a message is read."
  [sentence context]
  (let [lits (literals sentence)]                     ; one walk, read twice
    (into []
          cat
          [(when-not (context? context)
             [{:class :context-name :role :sentence :symbol context :literal nil}])
           (keep functor-problem lits)
           (for [pair lits
                 a    (args (second pair))
                 :let [p (argument-problem pair a)]
                 :when p]
             p)
           (ist-context-problems sentence)
           ;; a bare `.` is the dotted rest-pattern marker; it belongs inside a rule
           ;; antecedent, never as a top-level argument of an asserted sentence.
           (when (some #(= sx/dot-marker %) (args sentence))
             [{:class :dot-marker :role :sentence :symbol sx/dot-marker
               :literal sentence}])])))

(defn problems
  "Checkable naming violations for a sentence in a context (seq of strings): the
  context's own name, then every literal's functor (outermost wrapper first), then every
  literal's atomic symbol arguments, then any `ist` context slot, then the dotted rest
  marker where it cannot appear.

  **This is a check on the structure of a name, not on whether the name is worth having.**
  A *unary* snake_case functor is a well-formed type name, so
  `(implies (penguin ?x) (has_black_and_white_feathers ?x))` passes here, and so would
  `capable_of_swimming` or `thermoregulates_via_blubber_and_feathers` — each is exactly
  what the invariants say a type looks like.  Nothing about a symbol distinguishes a
  type the ontology wants from a one-off coined for a single sentence, so nothing here
  can refuse the second: judging that needs the KB's existing vocabulary, which is a
  separate question asked elsewhere.  Read this as a guard against *misnamed* content,
  never as a guard against vocabulary fragmentation."
  [sentence context]
  (mapv message (problems* sentence context)))

;; ---- the policy: whose invariants, and how hard ---------------------------
;;
;; The conventions above are what *this* KB reads a role off, and a KB holding a corpus
;; that spells its names differently is not thereby malformed — it is a KB whose front
;; entry point is set to a different opinion.  So the policy is per-KB (`open-kb`'s `:naming`),
;; not a property of the build: one process can hold a strict KB beside a corpus loaded
;; verbatim, and neither has to win.
;;
;; What the setting does **not** change is the role reading.  `predicate?` and its three
;; siblings answer the same way under every policy, so `:off` is a KB that stores a name
;; it cannot classify — `term-role` says nil, a `(Type Individual)` goal takes the general
;; path rather than the shortcut — rather than one that classifies differently.  That is
;; the whole cost, and it is why the check is worth keeping on where the content is
;; hand-written.

(def policies
  "What a KB does with a naming violation, and the one line each is for.

  A bulk path is not on this list because it does not consult it: a corpus import builds
  records directly and never asks (`docs/naming.md`, \"The two entry points\").  What it does
  instead is *report* — an operator learns the refused fraction at load time, from a
  count rather than from a failed experiment a year later."
  {:strict "refuse the assertion (the default: names stay legible)"
   :warn   "log each one and store anyway (a corpus being cleaned up)"
   :off    "store in silence (a corpus with its own spelling conventions)"})

(defn blocking-problems
  "The naming violations that **stop** something under `policy` — the messages, or nil.
  Empty under `:warn` and `:off` by construction, so a caller that has to yield a value
  rather than throw (`special/definitional-violation`, the `assert` dry run) asks this
  and needs no policy branch of its own."
  [policy sentence context]
  (when (= :strict policy) (seq (problems sentence context))))

;; ---- the other entry point: count what it would have refused ---------------------
;;
;; A bulk path stores what `assert` refuses, which is the point of having one — but a
;; store whose contents the public entry point disagrees with is a fact about that store, and the
;; only moment anybody is in a position to learn it cheaply is while the records are
;; going past.  So the bulk paths **count** what they do not check.  The tally is a
;; running map rather than a scan afterwards: a second pass over a corpus that needed a
;; bulk path in the first place is a second pass nobody will run.

(def empty-tally
  "A fresh `tally` accumulator: records seen, records with at least one violation, and
  the per-class breakdown.  Counts records rather than violations — one sentence can
  break three conventions, and what an operator is deciding is what fraction of the
  corpus is re-assertable."
  {:checked 0 :refused 0 :by-class {}})

(defn tally
  "Fold one sentence's violations into `t`.  Counts and classes only, never spellings: a
  corpus large enough to need a bulk path has a vocabulary large enough that holding its
  distinct offending names would cost more than the load
  (`vaelii.bench.survey`'s `naming` audit is where that question is asked)."
  [t sentence context]
  (let [ps (problems* sentence context)
        t  (update t :checked inc)]
    (if (empty? ps)
      t
      (-> t
          (update :refused inc)
          (update :by-class
                  #(reduce (fn [m c] (update m c (fnil inc 0)))
                           % (into #{} (map :class) ps)))))))

(defn tally-line
  "The one line a load prints about `t`, or nil when the public entry point agrees with the
  corpus — which is the common case and deserves no output at all."
  [t]
  (let [{:keys [checked refused by-class]} t]
    (when (pos? (long refused))
      (str (format "%,d of %,d records (%.1f%%) hold names `assert` would refuse: "
                   (long refused) (long checked)
                   (* 100.0 (/ (double refused) (double (max 1 checked)))))
           (str/join ", " (for [[c n] (sort-by val > by-class)]
                            (str (clojure.core/name c) " " (format "%,d" (long n)))))
           " — they are stored, findable and countable, but re-asserting one throws"
           " under :naming :strict"))))

;; Advice already given in this process, so a corpus of the same mistake is one line
;; rather than a line per fact.  `defonce` for the same reason the space counter is.
(defonce ^:private advised (atom #{}))

(defn- type-spelling
  "The type name a CapitalCamelCase symbol was reaching for: `Dog` is `dog`, and
  `PhysicalObject` is `physical_object` rather than `physicalobject` — types are
  snake_case, so lower-casing alone would suggest a name the conventions refuse."
  [s]
  (-> (nm s)
      (str/replace #"(?<=[a-z0-9])([A-Z])" "_$1")
      str/lower-case))

(defn advice
  "A well-formed sentence that is nonetheless almost certainly not what was meant — or
  nil.  Where `problems` reads the invariants, this reads *intent*, so everything here
  passes every check and stores cleanly.

  One entry so far.  `(isa Muffet Dog)` is the membership spelling every other KR system
  taught the reader, and here it stores a two-place predicate named `isa` relating two
  individuals — legal, indexed, believed, and matched by nothing anyone will ask.  The
  reader then asks `(isa? kb 'Muffet 'Dog)` and gets false, with no error to search for,
  because the type they meant was never asserted.  `CxCore.txt` says never to write
  it and `docs/naming.md` calls it out by name; neither is in front of someone who is
  typing.

  The bar for a new entry is that the shape has no legitimate reading: `isa` is a
  predicate no shipped KB declares and the one the ontology names as the mistake.  A
  shape somebody might mean stays out — a nudge that fires on correct input is one that
  gets tuned out, and takes the real ones with it."
  [sentence]
  (let [f     (functor sentence)
        [x t] (vec (args sentence))]
    (when (and (= 'isa f) (= 2 (arity sentence)))
      {:id      ::isa-is-not-how-membership-is-written
       :message (str "(isa " x " " t ") stores a two-place `isa` predicate, which nothing "
                     "reads — types here are unary predicates, so membership is written "
                     ;; the rewrite only where both arguments are symbols: an argument
                     ;; may legally be a number, a string or a compound term, and
                     ;; `clojure.core/name` throws on all three — advice that crashes
                     ;; the assert it was meant to help is worse than none
                     (if (and (symbol? x) (symbol? t))
                       (str "(" (type-spelling t) " " x ")")
                       "as a unary type predicate, (dog Muffet)")
                     " and the hierarchy with genl.  docs/naming.md")})))

(defn advise!
  "Log `advice` about `sentence`, once per process per kind of advice.

  Silent under `:naming :off`, which asks for names not to be policed at all.  Never a
  refusal at any policy: the sentence is well-formed, and refusing a legal shape on a
  guess about intent would make the public entry point unpredictable."
  [policy sentence context]
  (when (not= :off policy)
    (when-let [{:keys [id message]} (advice sentence)]
      (when-not (contains? @advised id)
        (swap! advised conj id)
        (trove/log! {:level :warn :id ::probably-not-meant
                     :msg  (str "stored, and probably not what was meant: " message)
                     :data {:sentence sentence :context context :advice id}})))))

(defn- refusal
  "The `:naming` refusal to throw, built with the `ExceptionInfo` **constructor** rather
  than `ex-info`.

  A refusal here is not a rare event, and that is by design.  The *checked* load — the
  entry point a corpus takes when the point is to learn what this KB makes of it, rather than the
  bulk path `tally` above is for — asserts one sentence at a time and **counts** what the
  public entry point refuses, because which of these checks an ontology trips is the most useful
  thing an import has to say about it.  So the throw is a reporting path taken a hundred
  thousand times in a load, and what it costs shows up as the load's own profile.

  `clojure.core/ex-info` (1.12) hands every exception it builds to `elide-top-frames`,
  which materializes the whole trace into a `StackTraceElement[]` via
  `Throwable.getStackTrace`, drops its own two frames and sets the array back — resolving
  every frame to a class, method and line number, for a trace a counted refusal never
  prints.  Since it walks the trace it materializes, the cost grows with how deep the
  refusing call sits, and an import refuses from the bottom of one: 6.3 µs against the
  constructor's 0.8 at the top of a stack, 23.7 against 4.4 forty frames down.  It is the
  largest single cost in a load that refuses most of what it reads.

  Nothing is lost by skipping it.  The frames elided are `ex-info`'s own, and the
  constructor's top frame is `check!` — where the refusal was decided."
  [ps sentence context]
  (ExceptionInfo. (str "naming invariant: " (str/join "; " ps))
                  {:type :naming :sentence sentence :context context}))

(defn check!
  "Enforce `policy` on `sentence` in `context`: throw `:naming` under `:strict`, log
  under `:warn`, do nothing under `:off`.  The one place the three differ, so no caller
  spells the throw out and none can drift from another.

  Past the invariants it also gives `advice` — for a sentence that breaks none of them
  and is still a mistake, which a refusal cannot reach."
  [policy sentence context]
  (when (not= :off policy)
    (when-let [ps (seq (problems sentence context))]
      (if (= :warn policy)
        (trove/log! {:level :warn :id ::naming-violation
                     :msg  (str "naming invariant (stored anyway, :naming :warn): "
                                (str/join "; " ps))
                     :data {:sentence sentence :context context}})
        (throw (refusal ps sentence context))))
    (advise! policy sentence context)))
