;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.naming
  "The naming invariants: predicates that read a symbol's role off its spelling, and the
  walk that applies them to every literal of a sentence, under the KB's `:naming` policy.
  Also the content-order comparator and keys every tie-break uses (docs/defenses.md,
  \"Tie-breaks and orderings key on content, not the handle\").  See docs/naming.md."
  (:refer-clojure :exclude [name])
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.sentex :as sx])
  (:import (clojure.lang ExceptionInfo)))

(defn- nm [s] (clojure.core/name s))

(def lexeme-namespace
  "The namespace that marks a **lexeme** (docs/naming.md)."
  "lex")

(defn lexeme?
  "Is `x` a lexeme, a symbol in the `lex` namespace (`lex/fool's_gold`)?  The other role
  predicates read a symbol's name half and answer false for a lexeme."
  [x]
  (and (symbol? x) (= lexeme-namespace (namespace x))))

(def context-namespace
  "The namespace of a reified context constant (docs/context-nat.md).  A literal, since
  `vaelii.impl.nat` requires this namespace."
  "cx")

(def reified-namespaces
  "The two namespaces a reified constant lives in: `nat` (an object) and `cx` (a context)
  (docs/nat.md).  A literal, since `vaelii.impl.nat-read` requires this namespace."
  #{"nat" context-namespace})

(defn reified-constant?
  "Is `x` a reified constant, a symbol in `nat/` or `cx/`?  The engine mints its name, so
  the name states no role, and `length-class` holds it to no length."
  [x]
  (and (symbol? x) (contains? reified-namespaces (namespace x))))

(defn context?
  "Is `x` a context: a `Cx…` CapitalCamelCase name, or a symbol in the `cx/` namespace?
  Decided by spelling alone, so a query context answers true."
  [x]
  (and (symbol? x) (not (lexeme? x))
       (or (= context-namespace (namespace x))
           (some? (re-matches #"Cx[A-Z][A-Za-z0-9]*" (nm x))))))

(def query-contexts
  "The **query contexts**: three `Cx…` symbols that name a reading mode rather than a
  place.  The read entry point resolves them, so nothing is stored in one and no `genlCx`
  edge names one.  `context?` answers true for each; `core/assert`'s context slot and
  the `genlCx` argument slots at `vaelii.impl.wff` refuse them.  What each one reads, and
  the variable context beside them: docs/contexts.md, \"The query contexts\"."
  '#{CxEverything CxInference CxNothing})

(defn query-context?
  "Is `x` one of `query-contexts`?"
  [x]
  (contains? query-contexts x))

(defn individual? [x] (and (symbol? x) (not (lexeme? x))
                           (some? (re-matches #"[A-Z][A-Za-z0-9]*" (nm x)))
                           (not (context? x))))
(defn function-spelled?
  "Is `x` an `individual?` whose name ends in `Fn` (`FatherFn`, `QuantityFn`), the
  spelling of a function?  `individual?` answers true for it as well; a relation slot in
  `vaelii.impl.wff` reads this to admit a function (docs/naming.md)."
  [x]
  (and (individual? x) (some? (re-matches #"[A-Z][A-Za-z0-9]*Fn" (nm x)))))
(defn predicate?  [x] (and (symbol? x) (not (lexeme? x))
                           (some? (re-matches #"[a-z][a-zA-Z0-9]*" (nm x)))))
(defn value?
  "Is `x` a value: neither a symbol nor a sequential compound?  A string, number, keyword,
  boolean, character, `nil` and a tagged literal (`#inst`, `#uuid`) each denote themselves,
  so each has instances of nothing.  A reified NAT is a `nat/` symbol, so it is no value."
  [x]
  (not (or (symbol? x) (sequential? x))))

(def ^:private disambiguator-re
  "A **sense**: a word, a `-`, and the disambiguator (`abrasive-grit`), split on the last
  dash (docs/naming.md).  The first character is `[a-z._]`, since the reader reads a
  leading digit as a number and a leading `'` as the quote macro; the word half admits
  no capital, and the disambiguator starts alphanumeric and carries no dash and no
  capital."
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

(defn predicate-spelled?
  "Is `x` spelled as a predicate of arity 2 or more: `predicate?` and not `type-symbol?`,
  so camelCase with an interior capital?  A bare lowercase word answers false."
  [x]
  (and (predicate? x) (not (type-symbol? x))))

(defn between-predicates?
  "Does `literal` have an argument, every one of them `predicate-spelled?`: the literals a
  `:forced-between-predicates` functor makes forced-monotonic (`decide/forced-literal?`),
  and the opposed bodies the index files under `[:opposed-between f]`."
  [literal]
  (boolean (and (next literal) (every? predicate-spelled? (rest literal)))))

(defn functor [sentence] (when (sequential? sentence) (first sentence)))
(defn args    [sentence] (when (sequential? sentence) (rest sentence)))
(defn arity   [sentence] (if (sequential? sentence) (dec (count sentence)) 0))

;; ---- a structural order on sentence / context content --------------------
;; docs/defenses.md, "Tie-breaks and orderings key on content, not the handle".

(defn print-key
  "`x` printed as a content key: `pr-str` with `*print-length*` and `*print-level*`
  released and `*print-meta*` off, so no ambient print bound collapses two keys to one.
  The one home for a printed ordering key; `compare-form` is the first choice, and this
  is for a key whose String order is the contract.  A symbol without metadata is `str`,
  with no binding frame.  `sort_by_content_key_test` fails a printed ordering key in
  `src/` that does not go through this fn or bind the print vars itself."
  ^String [x]
  (if (and (symbol? x) (nil? (meta x)))
    (str x)
    (binding [*print-length* nil *print-level* nil *print-meta* false]
      (pr-str x))))

(defn- form-rank
  "A total order on the kinds of value a sentence is built from, so `compare-form`
  orders a mixed pair where `clojure.core/compare` throws."
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
  "A structural total order on sentence and context content, as a `Comparator`.  It
  walks the two forms in place and reads no handle, so a tie breaks the same way in
  every arrival order.  Kinds order by `form-rank`; same-kind scalars by `compare`;
  two sequentials element by element, then shorter first, so `(a)` precedes `(a b)`.
  A value outside sentence content (a map, a set, a record) is compared by its
  `print-key`, so the order stays total under an ambient print bound."
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
  "`x` as a String ordering key where `x` is expected to be a scalar (a symbol, keyword,
  string or number): `str`, which no print bound elides for a scalar.  A collection is
  keyed through `print-key` instead, so a NAT or a sentence arriving here keys safely."
  ^String [x]
  (if (coll? x) (print-key x) (str x)))

(defn sort-by-content-key
  "`coll` ordered by `(keyfn element)` under `cmp`, as a vector.  The key is built once
  per element, where `sort-by` builds it once per comparison, and not at all below two
  elements.  `cmp` defaults to `compare-form`; pass `compare` for a pre-built
  `Comparable` key (a `[rank …]` tuple, a `print-key`).  The print vars are not bound
  here: a printed key goes through `print-key` in `keyfn`.  Stable, so equal keys keep
  `coll`'s order."
  ([keyfn coll] (sort-by-content-key keyfn compare-form coll))
  ([keyfn cmp coll]
   (let [v (vec coll)]
     (case (count v)
       (0 1) v
       ;; two, the length of most antecedent lists: one comparison; a tie keeps `coll`'s order
       2 (let [a (nth v 0) b (nth v 1)]
           (if (pos? (cmp (keyfn a) (keyfn b))) [b a] v))
       (->> v (mapv (fn [x] [(keyfn x) x])) (sort-by first cmp) (mapv second))))))

(defn min-by-content-key
  "`(first (sort-by-content-key keyfn cmp coll))` in one pass, building the key once per
  element.  A tie keeps the earliest element; nil for an empty `coll`.  `cmp` defaults
  to `compare-form`."
  ([keyfn coll] (min-by-content-key keyfn compare-form coll))
  ([keyfn cmp coll]
   (when-let [s (seq coll)]
     (second
      (reduce (fn [a b] (if (neg? (long (cmp (first b) (first a)))) b a))
              (map (fn [x] [(keyfn x) x]) s))))))

(defn by-print-key
  "`coll` ordered by its elements' `print-key` under `compare`: the guarded
  `(sort-by str coll)`, with the key built once per element."
  [coll]
  (sort-by-content-key print-key compare coll))

(defn distinct-by
  "Lazy `distinct` on `(f x)`, keeping the first element of each key in `coll`'s order.
  `levels` folds a derived answer into the stored one it duplicates with it, and
  `checks/first-per-slot` keeps one filler per slot."
  [f coll]
  (letfn [(step [xs seen]
            (lazy-seq
             (when-let [s (seq xs)]
               (let [x (first s), k (f x)]
                 (if (contains? seen k)
                   (step (rest s) seen)
                   (cons x (step (rest s) (conj seen k))))))))]
    (step coll #{})))

;; ---- the literals of a sentence ------------------------------------------
;; docs/naming.md, "Literals, wrappers, and arguments".

(def ^:private literal-roles
  "The wrapper a literal sits in, as a rejection message names it."
  {:sentence   "sentence"
   :antecedent "rule antecedent"
   :consequent "rule consequent"
   :exception  "exceptWhen exception"
   ;; a generator's generated rule (docs/generators.md)
   :generated-antecedent "generated rule antecedent"
   :generated-consequent "generated rule consequent"})

(def problem-classes
  "Each naming violation class `problems*` reports, with the line describing it.  The
  class is the datum a caller counts by; `message` renders the prose."
  {:context-name   "the KB context named is not a context"
   :functor        "a functor matching no convention"
   :functor-arity  "a snake_case functor (a unary predicate) at an arity other than 1"
   :functor-unary  "a camelCase functor at arity 1 — a unary predicate is snake_case"
   :lexeme-functor "a lexeme applied to arguments — a surface form names no relation"
   :argument       "a symbol argument matching no convention"
   :ist-context    "an ist context slot that does not name a context"})

(defn- rule-wrapper?
  "Is `h` one of the virtual wrappers around a single rule form (direction, defeasible,
  assumption, constraint, solve)?"
  [h]
  (or (contains? sx/rule-direction-wrappers h)
      (= sx/default-rule-wrapper h)
      (= sx/assumption-rule-wrapper h)
      (contains? sx/constraint-rule-wrappers h)
      (= sx/solve-rule-wrapper h)))

(defn- exception-query-conjuncts
  "The conjunct literals of an `exceptWhen` query, inside a `(set/monotonic Q)` wrapper
  when it has one: a vector is a conjunction, anything else one literal.  Read without
  canonicalizing, so a refused sentence interns no symbol."
  [q]
  (let [q (if (and (seq? q) (= sx/strength-wrapper (first q)) (= 2 (count q))) (second q) q)]
    (if (vector? q) q [q])))

(defn applied-literals
  "The `[role literal]` pairs of `sentence` as written: every position that applies
  something to arguments, tagged with the `literal-roles` key of the wrapper it sits in.
  Wrappers are descended and arguments are not.  A variable-functor position is
  included; `literals` filters it out and `rules/variable-functor-literals` keeps it."
  ([sentence] (applied-literals :sentence sentence))
  ([role form]
   (if-not (and (sequential? form) (seq form))
     []
     (let [h (first form)
           n (count form)]
       (cond
         ;; a `do/` imperative names no relation (`checks/check-no-imperative`)
         (sx/do-form? form) []

         ;; `(sentexHandle N)` names a stored sentex by integer id
         (= sx/sentex-handle-functor h) []

         (sx/variable? h) [[role form]]

         (rule-wrapper? h) (applied-literals role (second form))

         ;; `(exceptWhen <query> <rule-or-handle>)`: the query's conjuncts, then the rule
         (and (= sx/except-wrapper h) (= 3 n))
         (into (vec (mapcat #(applied-literals :exception %)
                            (exception-query-conjuncts (second form))))
               (applied-literals role (nth form 2)))

         (and (= sx/not-functor h) (= 2 n)) (applied-literals role (second form))

         (= sx/and-functor h) (vec (mapcat #(applied-literals role %) (rest form)))

         ;; A rule in consequent position is a generator's generated rule
         ;; (docs/generators.md): its literals are checked as a written rule's, and tagged
         ;; `:generated-*` at every nesting depth, the tag
         ;; `rules/variable-functor-literals` reads to admit a hole in functor position.
         (and (= sx/rule-functor h) (= 3 n))
         (let [gen?  (contains? #{:consequent :generated-consequent} role)
               arole (if gen? :generated-antecedent :antecedent)
               crole (if gen? :generated-consequent :consequent)]
           (into (vec (mapcat #(applied-literals arole %) (sx/rule-antecedents form)))
                 (applied-literals crole (sx/rule-consequent form))))

         ;; `(ist Ctx S)`: S is the literal, and `ist-context-problems` checks Ctx
         (and (= sx/ist-functor h) (= 3 n)) (applied-literals role (nth form 2))

         ;; negation as failure: `(unknown S)` and `(thereExists <vars> S)` wrap a
         ;; query, and a head `(exists <vars> C)` wraps the consequent it quantifies
         (sx/unknown? form)      (applied-literals role (second form))
         (sx/there-exists? form) (applied-literals role (nth form 2))
         (sx/head-exists? form)  (applied-literals role (sx/head-exists-body form))

         ;; `(forall ?v (implies B H))` desugars to a query over B's conjuncts and H
         ;; (`sx/desugar-forall-literal`), so each is read in the role the forall holds
         (and (sx/forall? form) (sx/implies? (nth form 2)))
         (let [body (nth form 2)]
           (vec (mapcat #(applied-literals role %)
                        (conj (sx/rule-antecedents body) (sx/rule-consequent body)))))

         ;; an aggregate's body is a goal, not an argument (docs/aggregate.md)
         (sx/aggregate? form)    (applied-literals role (sx/aggregate-body form))

         ;; `(bravely S)` / `(cautiously S)` read S over the current dilemmas
         ;; (docs/labeling.md)
         (and (contains? '#{bravely cautiously} h) (= 2 n)) (applied-literals role (second form))

         :else [[role form]])))))

(defn literals
  "The `[role literal]` pairs of `applied-literals` whose functor is not a variable: the
  functors an author named, which every check below reads."
  ([sentence] (literals :sentence sentence))
  ([role form]
   (filterv (fn [[_ lit]] (not (sx/variable? (first lit))))
            (applied-literals role form))))

;; ---- the invariants, per literal -----------------------------------------

(defn- camel-case
  "The camelCase spelling of a snake_case symbol, `lives_in` ⇒ `livesIn`, as a String."
  [s]
  (let [[head & more] (str/split (nm s) #"_+")]
    (apply str head (map str/capitalize more))))

(def unary-spelling-exempt
  "The camelCase functors legal at arity 1 because they name no relation
  (docs/naming.md, \"The one exemption\")."
  '#{sentexHandle})

(defn snake-case
  "The snake_case spelling of a camelCase symbol, `warmBlooded` ⇒ `warm_blooded`: the
  repair a `:functor-unary` rejection names."
  [s]
  (symbol (str/replace (nm s) #"([A-Z])" (fn [[_ c]] (str "_" (str/lower-case c))))))

(defn length-class
  "The class of the spelling violation a relation `f` of the lengths `binding` admits
  commits, or nil: `:functor-arity` when `f` is spelled as a type (underscored, or a
  sense) and `binding` admits no length of one, `:functor-unary` when `f` is camelCase,
  not `unary-spelling-exempt`, and `binding` admits the length one alone.  `binding` is
  `{:exact n}` or `{:min m}`; a bare lowercase word, a `reified-constant?` and a symbol
  matching no convention answer nil."
  [f {exact :exact floor :min}]
  (cond
    (or (not (symbol? f)) (reified-constant? f)) nil

    (and (type-symbol? f) (not (predicate? f))
         (if exact (not= 1 exact) (< 1 (long floor))))
    :functor-arity

    ;; the converse half of the biconditional.  A bare lowercase word satisfies
    ;; `type-symbol?` and never reaches this arm
    (and (predicate? f) (not (type-symbol? f)) (= 1 exact)
         (not (contains? unary-spelling-exempt f)))
    :functor-unary))

(defn- functor-problem
  "The naming violation of one `[role literal]` pair's functor, or nil:
  `:lexeme-functor`, `:functor`, `:functor-arity` or `:functor-unary`."
  [[role literal]]
  (let [f (functor literal)]
    (cond
      (nil? f) nil

      ;; a lexeme names no relation; as an argument it is ordinary
      (lexeme? f)
      {:class :lexeme-functor :role role :symbol f :literal literal}

      (not (or (predicate? f) (type-symbol? f)))
      {:class :functor :role role :symbol f :literal literal}

      :else
      (when-let [c (length-class f {:exact (arity literal)})]
        {:class c :role role :symbol f :literal literal}))))

(defn- pascal-case
  "The CapitalCamelCase spelling of an underscored symbol, `South_Pole` ⇒ `SouthPole`."
  [s]
  (apply str (map str/capitalize (str/split (nm s) #"_+"))))

(defn- argument-problem
  "The `:argument` violation of one argument `a` of a literal, or nil: a symbol matching
  no role.  A variable, the dotted rest marker and a non-symbol are not judged, and a
  compound argument is a term whose insides are not read."
  [[role literal] a]
  (when (and (symbol? a)
             (not (sx/variable? a))
             (not= sx/dot-marker a)
             (not (or (individual? a) (context? a) (predicate? a) (type-symbol? a)
                      (lexeme? a))))
    {:class :argument :role role :symbol a :literal literal}))

(defn- ist-context-problems
  "The `(ist Ctx S)` forms anywhere in `sentence`, arguments included, whose Ctx is
  neither a context name nor a variable, in depth-first pre-order.  `sx/forms-where`
  walks the tree without the lazy `tree-seq` this check runs over every assert."
  [sentence]
  (mapv (fn [f] {:class :ist-context :role :sentence :symbol (second f) :literal f})
        (sx/forms-where #(and (sequential? %)
                              (= sx/ist-functor (first %))
                              (= 3 (count %))
                              (not (or (sx/variable? (second %)) (context? (second %)))))
                        sentence)))

(defn message
  "One `problems*` map rendered as a rejection line: the offending symbol, the wrapper
  it sits in, and the spelling to write instead."
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
           ", which must start with Cx and continue CapitalCamelCase"))))

(defn problems*
  "The naming violations of `sentence` in `context`, as a vector of
  `{:class :role :symbol :literal}` maps in the order `problems` reports them.  `:class`
  is a `problem-classes` key, `:role` a `literal-roles` key, and `:symbol` the name
  that broke the convention."
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
           (ist-context-problems sentence)])))

(defn problems
  "The naming violations of `sentence` in `context`, as message strings: the context's
  name, then every literal's functor (outermost wrapper first), then every literal's
  atomic symbol arguments, then each `ist` context slot.  A check on the spelling of a
  name, not on whether the vocabulary wants it (docs/naming.md, \"What this does not
  check\")."
  [sentence context]
  (mapv message (problems* sentence context)))

;; ---- the policy: whose invariants, and how hard ---------------------------
;; docs/naming.md, "Whose invariants: the two policies".

(def policies
  "The `:naming` settings `open-kb` accepts, each with the line describing it."
  {:strict "refuse the assertion (the default: names stay legible)"
   :warn   "log each one and store anyway (a corpus being cleaned up)"
   :off    "store in silence (a corpus with its own spelling conventions)"})

(defn blocking-problems
  "The naming violations that stop a write under `policy`, as messages, or nil.  Nil
  under `:warn` and `:off`, so a caller that returns a value rather than throwing
  (`special/naming-violation`, `core/check`) has no policy branch of its own."
  [policy sentence context]
  (when (= :strict policy) (seq (problems sentence context))))

;; ---- the bulk paths: count what the checks would have refused --------------------
;; docs/naming.md, "Whose invariants: the two policies".

(def empty-tally
  "A fresh `tally` accumulator: records seen, records with at least one violation, and
  the records per violation class."
  {:checked 0 :refused 0 :by-class {}})

(defn tally
  "Fold one sentence's violations into `t`, counting records rather than violations.
  Counts and classes only, never spellings; `vaelii.bench.survey`'s `naming` audit
  groups by spelling."
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
  "The line a load logs about `t`, or nil when no record was refused."
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

;; The advice ids already logged in this process, so a corpus of one mistake logs one
;; line.  `defonce` keeps the set across a namespace reload.
(defonce ^:private advised (atom #{}))

(defn- type-spelling
  "The type name a CapitalCamelCase symbol stands for: `Dog` ⇒ `dog`, `WarmBlooded` ⇒
  `warm_blooded`."
  [s]
  (-> (nm s)
      (str/replace #"(?<=[a-z0-9])([A-Z])" "_$1")
      str/lower-case))

(defn advice
  "`{:id :message}` for a well-formed sentence that is almost certainly not what was
  meant, or nil.  One entry: `(isa X T)` at arity 2 (docs/naming.md, \"Advice\").

  The bar for a new entry is that the shape has no legitimate reading: `isa` is a
  predicate no shipped KB declares and the one the ontology names as the mistake.  A
  shape somebody might mean stays out, because a warning that fires on correct input
  is one an author learns to ignore."
  [sentence]
  (let [f     (functor sentence)
        [x t] (vec (args sentence))]
    (when (and (= 'isa f) (= 2 (arity sentence)))
      {:id      ::isa-is-not-how-membership-is-written
       :message (str "(isa " x " " t ") stores a two-place `isa` predicate, which nothing "
                     "reads — types here are unary predicates, so membership is written "
                     ;; the rewrite only where both arguments are symbols, since `name`
                     ;; throws on a number, a string or a compound
                     (if (and (symbol? x) (symbol? t))
                       (str "(" (type-spelling t) " " x ")")
                       "as a unary type predicate, (dog Muffet)")
                     " and the hierarchy with genl.  docs/naming.md")})))

(defn advise!
  "Log `advice` about `sentence` at `:warn`, once per process per advice id.  Silent
  under `:off`; never a refusal."
  [policy sentence context]
  (when (not= :off policy)
    (when-let [{:keys [id message]} (advice sentence)]
      (when-not (contains? @advised id)
        (swap! advised conj id)
        (trove/log! {:level :warn :id ::probably-not-meant
                     :msg  (str "stored, and probably not what was meant: " message)
                     :data {:sentence sentence :context context :advice id}})))))

(defn- refusal
  "The `:naming` refusal, built with the `ExceptionInfo` constructor rather than
  `ex-info`, which materializes the stack trace to elide its own frames
  (docs/defenses.md, \"A naming refusal skips `ex-info`\").  Same class, message and
  ex-data; the top frame is `check!`."
  [ps sentence context]
  (ExceptionInfo. (str "naming invariant: " (str/join "; " ps))
                  {:type :naming :sentence sentence :context context}))

(defn check!
  "Enforce `policy` on `sentence` in `context`: throw `:naming` under `:strict`, log
  under `:warn`, do nothing under `:off`.  Under `:strict` and `:warn` it then logs any
  `advice`."
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

;; ---- a length binding against its relation's spelling ---------------------
;; docs/naming.md, "A length binding is held to the spelling".

(defn binding-problem
  "The spelling violation of the length binding `sentence` states (`sx/arity-binding`),
  as `{:class :symbol :binding}`, or nil: `length-class` of the bound relation over the
  lengths the binding admits, `{:exact n}` or `{:min m}`.  A `variable_arity` binding
  admits every length and breaks no spelling."
  [sentence]
  (when-let [[q kind v] (sx/arity-binding sentence)]
    (when-let [b (case kind :exact {:exact v} :min {:min v} nil)]
      (when-let [c (length-class q b)]
        {:class c :symbol q :binding b}))))

(defn- binding-message
  "The rejection line for `binding-problem`'s answer `p` about `sentence`."
  [sentence {:keys [class symbol binding]}]
  (let [said (if-let [n (:exact binding)]
               (str "binds " symbol " to " n (if (= 1 n) " argument" " arguments"))
               (str "binds " symbol " to " (:min binding) " arguments or more"))]
    (case class
      :functor-arity
      (str (pr-str sentence) " " said ", but " symbol " is snake_case, which names a"
           " unary predicate — bind a relation spelled camelCase, "
           (camel-case symbol) ", or bind " symbol " to one argument")
      :functor-unary
      (str (pr-str sentence) " " said ", but " symbol " is camelCase, which names a"
           " relation of two or more arguments — a one-place predicate is spelled "
           (snake-case symbol)))))

(defn check-binding!
  "Enforce `policy` on the length binding `sentence` states (`binding-problem`): throw
  `:length-against-spelling` under `:strict`, carrying `:relation`, `:class` and
  `:binding`, log under `:warn`, do nothing under `:off`."
  [policy sentence context]
  (when (not= :off policy)
    (when-let [p (binding-problem sentence)]
      (let [m (binding-message sentence p)]
        (if (= :warn policy)
          (trove/log! {:level :warn :id ::binding-spelling
                       :msg  (str "length binding against its spelling (stored anyway,"
                                  " :naming :warn): " m)
                       :data {:sentence sentence :context context}})
          (throw (ex-info m {:type :length-against-spelling :sentence sentence
                             :context context :relation (:symbol p) :class (:class p)
                             :binding (:binding p)})))))))
