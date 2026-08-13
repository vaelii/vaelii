;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.sentex
  "The sentex — Vaelii's unit of knowledge: a sentence paired with the context it
  holds in (sentence + context = sentex).

  A *sentence* is a logical form written as a Clojure s-expression, e.g.
  (parentOf Tom Bob).  Ground (all constants) or a *pattern* with variables like ?x.
  A *context* names the situation / assumption frame it is asserted within.

  The structural connectives `not`, `implies`, and `and` are **canonicalized into
  the record** rather than left as data: a sentex carries a `truth` (`:true` /
  `:false`, with double negation eliminated), and — for a rule — a decomposed
  `antecedent` (vector of patterns) and `consequent`.  So the connectives never
  reach the inverted **term index** (their heads are stripped, even nested inside a
  rule — see `content-forms`), and the positional **trie key** drops the
  `implies` / `and` rule frame; a negative literal keeps its `not` there as its
  *polarity*, so a rule concluding `(flies ?x)` and one concluding `(not (flies ?x))`
  get distinct keys.

  Beyond the connectives, a sentence is put into a **canonical form** so that
  logically identical knowledge is stored once:

    * **canonical variables** — a rule's variables are renamed `?var0`, `?var1`, …
      by first occurrence in canonical order, and `:varmap` maps them back to what
      the author wrote (`{?var0 ?x}`), so display can restore the original names.
    * **canonical literal order** — a rule's antecedents are sorted by a
      *structural* order (polarity, arity, ground arity, variable degree, shape),
      falling back to a lexical comparison of constants only as the last resort.
      Variables compare by their canonical *index*, never by name.
    * **symmetric arguments sorted** — `(siblingOf Bob Ann)` and `(siblingOf Ann Bob)`
      canonicalize to one sentex when `siblingOf` is declared symmetric.
    * **comparison siblings folded** — `greaterThan` is stored as `lessThan` with
      its arguments reversed, so only the `<` direction is ever stored.
    * **comparison chains collapsed** — `lessThan` is variable-arity, and chained
      comparisons in a rule merge: `(lessThan ?a ?b)` + `(lessThan ?b ?c)` becomes
      the single literal `(lessThan ?a ?b ?c)`.  `different` gets **neither** fold:
      it is not transitive, so a merged chain would claim more than was asserted.

  An `exceptWhen` exception does not touch the rule record: it is stored separately as
  a meta-sentex naming the rule by handle (see the `RuleSentex` field notes below).

  `:sentence` holds the canonical, readable form for display and matching.

  A sentex is one of two records — `AtomicSentex` (an atomic sentence: a fact, a metadata
  declaration, a query pattern) or `RuleSentex` (an implication) — so an atomic sentex does
  not carry the rule-only slots (there are 100M+ of them), and each still round-trips
  through nippy with its type intact."
  (:refer-clojure :exclude [name])
  (:require [vaelii.impl.caches :as caches])
  (:import [java.util.concurrent ConcurrentHashMap]))

;; Two records, split so an atomic sentex does not carry the seven rule-only slots
;; (facts are the 100M+ case).  Both share the scalar core:
;;   sentence    the canonical, readable form — `(not S)` for a negative literal,
;;               `(implies (and …) …)` for a rule; display and matching read it
;;   context     the context symbol it holds in
;;   id          the integer handle, nil until the record store assigns one
;;   truth       :true | :false        (a `(not S)` becomes S at :false)
;;   strength    :monotonic | :default | nil    (the assumption strength when the
;;               sentex is asserted as a premise; nil for a purely-derived one)
;;
;; An `AtomicSentex` is an atomic sentence — a fact, a metadata declaration, or a query
;; pattern: one signed predicate application, ground or holding variables.  It adds
;; nothing to the core, and reading any rule-only key off it returns nil, so
;; `(some? (:antecedent sx))` is the atomic-vs-rule discriminant everywhere.
(defrecord AtomicSentex [sentence context id truth strength])
;;
;; A `RuleSentex` is an implication.  Beyond the core it carries the decomposition the
;; connectives and `set/*` wrappers canonicalize into:
;;   antecedent  [pattern ...]          (the antecedents — the sentence's `and` body)
;;   consequent  pattern                (the consequent)
;;   varmap      {?var0 ?x, …} | nil    (canonical variable -> the author's name)
;;   direction   :forward | :backward | :both | :inert   (from its set/*Rule wrapper;
;;               :both for a bare implies)
;;   defeasible  true | nil             (a set/defaultRule rule: its conclusions are
;;               defeasible and fire in the defaults phase)
;;   assumption  true | nil             (a set/assumptionRule: the rule's head is a
;;               *choice* for a solve, not a derived truth.  It never forward-chains
;;               into belief; a solve grounds it (docs/solving.md).  It is part of the
;;               rule's identity — in the trie key — so a choice rule and its bare twin
;;               are different sentexes)
;;   constraint  :hard | :soft | nil    (a set/hardConstraint / set/softConstraint rule:
;;               the head is a *contradiction marker*, and the rule's body is a
;;               conjunctive nogood mixing background facts and choice-head patterns.
;;               Like an assumptionRule it never forward-chains; a solve grounds its body
;;               into nogoods (soft) or integrity constraints (hard).  Part of the rule's
;;               identity — in the trie key — so a constraint rule and its bare twin are
;;               different sentexes.  See docs/solving.md)
;;
;; An `exceptWhen` exception is **not** a Rule field: it is a separate belief-following
;; meta-sentex `(exceptWhen <query> (sentexHandle <rule-id>))` naming the rule it
;; qualifies (`exceptWhen-meta`), so a rule and its unexcepted twin share one handle
;; and asserting or retracting an exception amends the rule in place.  The engine reads
;; a rule's exceptions from those meta-sentexes (`provers/rule-exceptions`), never off
;; the record.
(defrecord RuleSentex [sentence context id truth antecedent consequent strength varmap
                       direction defeasible assumption constraint])

(def ^:dynamic *symbol-pool-limit*
  "The most distinct symbols the pool holds before it is cleared wholesale.  Sized well
  above any real *vocabulary* — the shipped ontology plus the whole of OpenCyc is ~188k
  constants — so a KB that only ever names things never reaches it and keeps every name
  shared, which is the entire point of the pool.  A cap a normal load could touch would
  throw away the sharing it exists for; this one is reached only by a minter running per
  fact.  Dynamic for the reason `taxonomy/*scoped-memo-budget*` is: the only way to
  exercise the flush is to make it happen."
  1000000)

(def ^:private symbol-pool
  "Interns the symbols sentences are built from, so the same predicate, individual,
  type, context, or variable name is a single shared object across every sentex that
  mentions it — the sharing a `parentOf` repeated through 100M+ facts buys, which
  dwarfs the pool's own footprint.  A `ConcurrentHashMap` because readers may intern
  beside the single writer.

  What bounds it is **not** the vocabulary.  A KB that only names things holds one entry
  per distinct name and is ontology-sized, but three writers mint a *fresh* symbol per
  fact: NAT reification (`nat/fresh-constant`, one `nat/g…` per reified non-atomic
  term), head-existential skolemization (`skolem/skolemize-conclusion`, one witness per
  existential per firing frontier) and abduction (one scratch context each).
  Under any of those the pool grows with the fact count rather than with the ontology,
  and nothing hands an entry back: it is static, process-wide and shared by every KB in
  it, so `retract!`, the store clears, `core/clear!`, a KB close and a catalog switch all
  leave it exactly as large as it was.

  So it is capped at `*symbol-pool-limit*` and cleared **wholesale** when full, the shape
  the other bounded caches here take (`taxonomy/*scoped-memo-budget*`,
  `observe/resident-limit`, `stp/closure-cache-limit`).  A clear can change no answer,
  only a footprint: interning changes identity and never equality, so the symbols already
  stored stay alive in the records holding them, keep comparing and hashing exactly as
  they did, and are re-pooled on their next mention.  What it costs is the sharing for
  the names minted before it — which is the trade a pool that cannot be emptied does not
  get to make."
  (ConcurrentHashMap.))

(defn intern-sym
  "The pooled instance of symbol `s` (or `s` unchanged when it is not a symbol).
  Interning changes identity, never equality, so a pooled `?var0` still matches a
  fresh one as a binding key.

  The size check rides the **miss** path, so a repeated name pays a bare `.get` and only
  a genuinely new one consults the count.  A reader whose `.get` loses a race with a
  concurrent clear falls back to its own instance: a missed sharing, never a wrong
  symbol, which is the same reason the wholesale clear is safe at all."
  [s]
  (if (symbol? s)
    (let [^ConcurrentHashMap p symbol-pool]
      (or (.get p s)
          (do (when (<= (long *symbol-pool-limit*) (.size p)) (.clear p))
              (.putIfAbsent p s s)
              (or (.get p s) s))))
    s))

;; No `:clear`, and the pool is the one cache here where that is a decision rather than
;; an omission: dropping it changes no answer (interning moves identity, never equality)
;; but throws away the sharing every symbol minted before it was paying for, and buys no
;; measurement in return — nothing counts a pool hit.  The wholesale clear at the limit
;; is a footprint ceiling, not an instrument.
(caches/register-cache
 {:cache    :symbol-pool
  :label    "Symbol pool"
  :scope    :process
  :unit     "symbols"
  ;; a thunk, not the value: the var is dynamic precisely so a caller can rebind it, and
  ;; a bound captured at load would report the root while the pool enforced the binding
  :limit    (fn [] *symbol-pool-limit*)
  :counters nil
  :note     (str "One shared object per distinct predicate, individual, type, context "
                 "or variable name, across every KB in this process. Bounded by the "
                 "vocabulary until something mints a symbol per fact — reification, "
                 "skolemization, an abduction's scratch context — after which it grows "
                 "with the fact count and nothing hands an entry back.")
  :read     (fn [_] {:entries (.size ^ConcurrentHashMap symbol-pool)})})

(defn canon
  "Canonicalize a sentence to a single sequential representation (PersistentList,
  recursively), interning every symbol through `symbol-pool` on the way.  Substitution
  and reads produce lazy seqs / vectors that are `=` but freeze to *different* nippy
  bytes; canonicalizing before anything reaches a key or value keeps trie keys and
  dedup stable, and the interning collapses the repeated vocabulary to shared objects
  — the trie key reuses them for free, since it passes constant symbols through
  unchanged."
  [x]
  (cond
    (symbol? x)     (intern-sym x)
    (sequential? x) (apply list (map canon x))
    :else           x))

(defn intern-deep
  "`x` with every symbol replaced by its pooled instance, **preserving shape** — a list
  stays a list and a vector a vector.  `canon` is the other half of the same pair and
  flattens both to a list, which is right for a sentence and wrong for anything already
  canonical that is being rebuilt from bytes: a rule's `:antecedent` is a vector and a
  `[::subterm k]` marker must stay one.

  So this is what every path *back into memory* uses — the record frames
  (`vaelii.impl.disk.codec`) and the index snapshot's token dictionary
  (`vaelii.impl.disk.index-snapshot`).  Without it a thawed structure holds a private
  copy of every name it mentions, which on a store whose whole point is that the
  vocabulary is written once is the one cost that must not be paid per record."
  [x]
  (cond
    (symbol? x)     (intern-sym x)
    (vector? x)     (mapv intern-deep x)
    (map? x)        (persistent!
                     (reduce-kv (fn [m k v] (assoc! m (intern-deep k) (intern-deep v)))
                                (transient {}) x))
    (sequential? x) (apply list (map intern-deep x))
    :else           x))

(defn variable?
  "A pattern variable is a symbol whose name starts with '?', plus the anonymous
  wildcard _.  Variables act as wildcards during index lookup and as logic
  variables during unification."
  [x]
  (and (symbol? x)
       ;; hinted explicitly rather than left to inference off `name`'s own `^String`:
       ;; this is the engine's most-called predicate (`substitute` calls it per term),
       ;; and a rewriter that reaches the form without the inference — cloverage's
       ;; instrumentation does — turns the interop into a reflective `getMethods` copy
       ;; per call.  The hint is what makes the dispatch direct no matter who reads it.
       (let [^String n (clojure.core/name x)]
         (or (= n "_") (.startsWith n "?")))))

(defn- form-vars
  "Every variable anywhere in a form, in order of occurrence."
  [form]
  (filter variable? (tree-seq sequential? seq form)))

(defn some-symbol?
  "Does any symbol anywhere in `form` satisfy `pred`?  Short-circuits on the first.

  A direct walk rather than `some` over `tree-seq`, for the reason `chain`'s
  `free-consequent-vars` is one: this runs per stored sentex on paths that ask it of
  every match in an answer set, the form is usually `(pred a b)`, and the lazy seq
  `tree-seq` builds costs several times the three `cond` arms it describes.  Nothing is
  allocated on the overwhelmingly common false answer."
  [pred form]
  (letfn [(walk [x]
            (cond (sequential? x) (reduce (fn [_ y] (if (walk y) (reduced true) false)) false x)
                  (symbol? x)     (boolean (pred x))
                  :else           false))]
    (walk form)))

(defn symbols-where
  "The set of symbols anywhere in `form` satisfying `pred`, or **nil** when none does.
  The collecting form of `some-symbol?`, and nil rather than `#{}` so a caller can gate
  on it without allocating for the common empty answer."
  [pred form]
  (letfn [(walk [acc x]
            (cond (sequential? x)              (reduce walk acc x)
                  (and (symbol? x) (pred x))   (conj (or acc #{}) x)
                  :else                        acc))]
    (walk nil form)))

;; ---- virtual rule wrappers (canonicalized into the record) ---------------
;; `(set/forwardRule (implies …))` is not data about a rule — it *is* how the rule's
;; direction is written.  Like not / implies / and, the wrapper canonicalizes into
;; the record (`:direction`, `:defeasible`, `:assumption`) and never reaches the stored
;; sentence, so a rule carries its own direction rather than it living in a side index.
;; (`exceptWhen` is the exception: it is split off at the assert layer and stored as a
;; separate meta-sentex, not folded into the record — see `exceptWhen-meta`.)

(def rule-direction-wrappers
  '{set/forwardRule :forward, set/backwardRule :backward, set/inertRule :inert})

(def default-rule-wrapper 'set/defaultRule)

(def assumption-rule-wrapper
  "`(set/assumptionRule (implies …))` — the rule's head is a *choice* offered to a
  solve, not a truth to derive.  Canonicalizes into `:assumption`; the rule never
  forward-chains into belief and is consulted only when grounding a solve
  (docs/solving.md)."
  'set/assumptionRule)

(def constraint-rule-wrappers
  "`(set/hardConstraint (implies …))` / `(set/softConstraint (implies …))` — the rule's
  head is a *contradiction marker* and its body a conjunctive nogood over background
  facts and choice-head patterns.  Canonicalizes into `:constraint` (`:hard` / `:soft`);
  like an assumptionRule the rule never forward-chains, and a solve grounds its body
  (docs/solving.md).  A hard constraint renders as an ASPIF integrity constraint (models
  violating it are excluded); a soft one as a minimized violation."
  '{set/hardConstraint :hard, set/softConstraint :soft})

(def except-wrapper
  "`(exceptWhen <query> <rule>)` — the rule does not conclude for a binding its
  exception holds of.  Unlike the other wrappers this one takes *two* arguments and
  captures one: the query.  The wrapper is split off at the assert layer and stored as
  a `(exceptWhen <query> (sentexHandle <rule-id>))` meta-sentex naming the rule, rather
  than folded into the rule record (see `exceptWhen-meta`)."
  'exceptWhen)

(defn exception-conjuncts
  "Normalize an `exceptWhen` query to its one internal shape — a vector of literals,
  *all* of which must hold.  A conjunction is written as a vector, the way
  `core/prove` spells one; a single literal may be written bare."
  [form]
  (if (vector? form) (mapv canon form) [(canon form)]))

(defn check-exception-closed
  "Throw unless the `exceptWhen` exception is **closed** over `antecedents`: every
  variable it mentions is bound before it runs, so it is a ground existence check
  rather than a search for bindings.  The mirror of
  `rules/check-range-restricted`, pointed at the exception instead of the
  consequent.

  This forbids an *existential* exception — \"birds fly unless they have a sick
  child\" is not expressible, because `?child` would be unbound.  docs/exceptions.md
  records that as a deliberate limit and the price of the ground check; the
  workaround is an antecedent that binds the witness."
  [antecedents exception]
  ;; `_` is an anonymous wildcard: two occurrences are two *different* variables, so
  ;; an antecedent can never bind one for the exception to read.
  (when-let [w (seq (filter #(= '_ %) (mapcat form-vars exception)))]
    (throw (ex-info "exception uses the anonymous wildcard _, which binds nothing"
                    {:type :exception-not-closed :unbound (vec w)
                     :exception (vec exception) :antecedents (vec antecedents)})))
  (let [bound (into #{} (mapcat form-vars) antecedents)
        loose (distinct (remove bound (mapcat form-vars exception)))]
    (when (seq loose)
      (throw (ex-info (str "exception is not closed: " (pr-str (vec loose))
                           " unbound by the rule's antecedents")
                      {:type :exception-not-closed :unbound (vec loose)
                       :exception (vec exception) :antecedents (vec antecedents)})))))

(defn peel-rule-wrapper
  "Strip the virtual rule wrappers, returning
  [direction defeasible exception assumption constraint inner].  Wrappers may nest in
  any order — a defeasible forward rule with an exception, an assumption rule, a hard
  constraint — and two `exceptWhen`s conjoin.  `exception` is nil or a vector of
  literals; `assumption` is true or nil; `constraint` is `:hard` / `:soft` or nil."
  [form]
  (loop [f form, dir nil, def? nil, exc nil, assum nil, con nil]
    (if (and (sequential? f) (seq f))
      (let [h (first f)]
        (cond
          (= h default-rule-wrapper)    (recur (second f) dir true exc assum con)
          (= h assumption-rule-wrapper) (recur (second f) dir def? exc true con)
          (constraint-rule-wrappers h)  (recur (second f) dir def? exc assum (constraint-rule-wrappers h))
          (rule-direction-wrappers h)   (recur (second f) (rule-direction-wrappers h) def? exc assum con)
          (and (= h except-wrapper) (= 3 (count f)))
          (recur (nth f 2) dir def? (into (or exc []) (exception-conjuncts (second f))) assum con)
          :else                         [dir def? exc assum con f]))
      [dir def? exc assum con f])))

;; ---- structural connectives (canonicalized into the record) -------------

(def not-functor  'not)
(def rule-functor 'implies)
(def and-functor  'and)
(def ist-functor  'ist)
(def dot-marker   '.)

;; ---- sentex handles: a stored sentex as a term --------------------------
;; A handle is `(sentexHandle <id>)` — the term form of a stored sentex's integer
;; handle, so a *meta-sentex* (`exceptWhen`, `except`) can name another sentex as an
;; argument.  The id is a plain integer, so the term index drops it but keeps the whole
;; compound: a meta-sentex is findable by the handle it names (`find-sentexes` on the
;; handle) and never by the id alone.  That key is the one direct read on the firing
;; path (`provers/rule-exceptions`), and it is a *nested* subterm of the meta, so
;; `*min-indexed-depth*` keeps it at its default — the floor drops a literal's own key,
;; not the terms inside one.  Order-independence holds because the engine's
;; invariant is over *beliefs*, not raw handle ids (order_independence_test) — two
;; assertion orders give a rule different ids but the same beliefs, and a meta-sentex
;; naming it follows suit.  Handle lookup is `handle-id` → `p/get-sentex`.

(def sentex-handle-functor 'sentexHandle)

(def except-functor
  "`(except <handle>)` — a meta-sentex removing visibility of the sentex the handle
  names from the context it is asserted in and that context's descendants (everything
  that *sees* it).  A ground fact — the handle is ground — belief-following like any
  other, so retracting or defeating the `except` restores the hidden sentex."
  'except)

(defn sentex-handle
  "The handle term naming the sentex stored at id `n`."
  [n] (list sentex-handle-functor (long n)))

(defn sentex-handle?
  "Is `form` a `(sentexHandle <id>)` term?"
  [form]
  (and (sequential? form)
       (= sentex-handle-functor (first form))
       (= 2 (count form))
       (integer? (second form))))

(defn handle-id
  "The sentex id a handle names, or nil when `form` is not a handle."
  [form]
  (when (sentex-handle? form) (long (second form))))

;; ---- exceptWhen as a meta-sentex ----------------------------------------
;; An exceptWhen exception is stored as `(exceptWhen <query> (sentexHandle <rule-id>))`
;; — a meta-sentex naming the rule it qualifies.  The query is a single literal (bare)
;; or a conjunction (an `(and …)` wrap), in the rule's *canonical* variables, so a
;; firing's bindings substitute straight in.  It is an ordinary belief-following fact,
;; so retracting or defeating it lifts the exception; the whole `(sentexHandle H)` is a
;; ground compound, so the term index makes the rule's exceptions findable by handle.

(defn exceptWhen-meta
  "The exceptWhen meta-sentence for `conjuncts` (a seq of literals, all of which must
  hold) qualifying the rule at `rule-id`.  A single literal is stored bare, several as
  an `(and …)` — canon-stable either way (a vector would flatten to a list and lose the
  shape)."
  [conjuncts rule-id]
  (let [cs (vec conjuncts)
        q  (if (= 1 (count cs)) (first cs) (apply list and-functor cs))]
    (list except-wrapper (canon q) (sentex-handle rule-id))))

(defn exceptWhen-meta?
  "Is `sentence` a `(exceptWhen <query> (sentexHandle <id>))` meta-sentex — the stored
  form, whose second argument is a handle (as opposed to the `(exceptWhen <query>
  <rule>)` *wrapper*, whose second argument is a rule form)?"
  [sentence]
  (and (sequential? sentence)
       (= except-wrapper (first sentence))
       (= 3 (count sentence))
       (sentex-handle? (nth sentence 2))))

(defn exceptWhen-rule-handle
  "The rule handle an exceptWhen meta-sentence names."
  [sentence]
  (when (exceptWhen-meta? sentence) (handle-id (nth sentence 2))))

(defn exception-query-conjuncts
  "The conjunct literals of an exceptWhen meta-sentence's query — the inner `(and …)`
  unwrapped, or a bare single literal as a one-element vector.  The inverse of
  `exceptWhen-meta`."
  [sentence]
  (let [q (nth sentence 1)]
    (if (and (sequential? q) (= and-functor (first q)))
      (vec (rest q))
      [q])))

(def do-namespace
  "The namespace marking an **imperative** — a form given to `assert` that instructs
  the engine to do something rather than stating that something is true.
  `(do/labeling Ctx)` is the first (docs/labeling.md).

  It parallels `set/`, which sets a field on the rule it wraps, and `ist`, which is
  likewise given to `assert` and likewise never stored.  Nothing in the `do/`
  namespace is ever a sentex: there is no fact to store, only an action to take."
  "do")

(defn do-form?
  "Is `form` a `do/` imperative?

  Used both to dispatch one at the top level of `assert` and to **refuse** one
  anywhere it would run inside a fixpoint — a rule antecedent, a rule consequent, an
  `exceptWhen` query, or anything derived.  Forward chaining's defining property is
  that the same knowledge in any order yields the same beliefs; an imperative firing
  during it would run a number of times that depends on firing order, and would mutate
  the KB the fixpoint is still computing over.  That breaks order independence and
  locality at once (docs/nmtms.md), so `do/` is legal only where a caller put it:
  at the top level of an `assert`, once, after settling."
  [form]
  (and (sequential? form)
       (symbol? (first form))
       (= do-namespace (namespace (first form)))))

(defn- negation? [form]
  (and (sequential? form) (= not-functor (first form)) (= 2 (count form))))

(defn implies?
  "Is `form` a rule form `(implies <ante> <conseq>)`?  Arity checked: an `implies` at
  any other arity is never read as a rule — `rule-consequent` is an `nth`, and an
  arity-4 form read as a rule silently dropped its tail.  `connective-problems`
  refuses the malformed form at both doors before this question is asked."
  [form]
  (and (sequential? form) (= rule-functor (first form)) (= 3 (count form))))

(defn- peel-not
  "Strip leading `not` wrappers, returning [truth body] with double negation
  eliminated: an even number of nots ⇒ :true, an odd number ⇒ :false."
  [form]
  (loop [f form, positive true]
    (if (negation? f)
      (recur (second f) (not positive))
      [(if positive :true :false) f])))

(defn rule-antecedents
  "The antecedent patterns of a rule form (unwrapping a leading `and`; a single
  antecedent needs no `and`)."
  [form]
  (let [a (second form)]
    (if (and (sequential? a) (= and-functor (first a))) (vec (rest a)) [a])))

(defn rule-consequent
  "The consequent pattern of a rule form."
  [form]
  (nth form 2))

;; ---- aggregation: counting what the KB believes --------------------------
;; `(agg/count ?n ?v <body>)` and its four siblings are the third member of the
;; `unknown` / `thereExists` family: query operators, answered by a prover
;; (`vaelii.impl.provers/AggregateProver`), refused by `wff` as assertions, and never
;; stored.  `?v` is **projected out** exactly as a `thereExists` binder is — it is
;; counted, not witnessed — and `?n` is the only binding the operator produces.  They
;; live up here, above the canonicalization, because the deferred set below is built
;; from them.  See docs/aggregate.md.

(def aggregate-functors
  "The five aggregation operators, mapped to the reduction each names.  Every one has
  the same shape — `(<op> ?n ?v <body>)`, four elements — so one prover answers all
  five and one frame arm covers them everywhere a form is walked."
  '{agg/count :count
    agg/sum   :sum
    agg/min   :min
    agg/max   :max
    agg/avg   :avg})

(defn aggregate?
  "Is `form` an `(<aggregate-op> ?n ?v <body>)` literal?"
  [form]
  (and (sequential? form) (= 4 (count form))
       (contains? aggregate-functors (first form))))

(defn aggregate-value-var
  "The variable an aggregate reduces over — the one projected out.  Nil when the slot
  holds something that is not a variable, which `wff` refuses separately."
  [form]
  (let [v (nth form 2)] (when (variable? v) v)))

(defn aggregate-body
  "The query an aggregate reduces the solutions of."
  [form] (nth form 3))

;; ---- comparison siblings: only the `<` direction is ever stored ----------

(def comparison-siblings
  "Comparison predicates that fold onto a canonical sibling by reversing their
  arguments, so `(greaterThan A B)` is stored as `(lessThan B A)`.  Add a pair here
  and both directions canonicalize to one literal."
  '{greaterThan lessThan})

(def chained-comparisons
  "Variable-arity, transitive comparisons whose chains collapse into one literal:
  `(lessThan ?a ?b)` + `(lessThan ?b ?c)` ⇒ `(lessThan ?a ?b ?c)`."
  '#{lessThan})

(def deferred-predicates
  "Predicates that *consume* bindings rather than produce them — evaluable tests and
  computations.  Antecedent order is operational for these: `(evaluate ?z (+ ?x ?y))`
  can only run once `?x`/`?y` are bound, so they must stay after the literals that
  bind them.  Canonical ordering therefore keeps them last, in the author's relative
  order (one computation may feed the next).

  `different` is here for the same reason and no other.  It is a ground-only test
  over the equality closure (`vaelii.impl.provers`), so a `different` antecedent
  sorted ahead of the literal that binds its variables is not merely slow — it is
  inapplicable, and the rule silently stops firing.

  Being deferred is *all* `different` shares with the comparisons: it is deliberately
  absent from `comparison-siblings` and `chained-comparisons` below.  The obvious
  analogy is wrong.  `lessThan` merges chains because it is **transitive** — `a<b`
  and `b<c` give `a<b<c` for free — whereas `different` is **not**: `A≠B` and `B≠C`
  say nothing whatever about `A` and `C`, so merging `(different A B)` with
  `(different B C)` into `(different A B C)` would manufacture a pairwise claim
  nobody asserted.  The only sound merge would be a clique (every pair present),
  which is more machinery than the feature is worth.  And since `different` is never
  stored, there is nothing to canonicalize *for*: canonical form exists so that
  logically identical knowledge stores once, and this stores never.  See
  docs/equality.md.

  `unknown` is here for the same operational reason: `(unknown S)` is **negation as
  failure** — it holds exactly while `S` is *not* derivable — so it consumes the
  bindings its argument's free variables need and produces none.  Reaching it before
  those bindings exist would test an open sentence, which is meaningless, so like
  `different` it is pinned after the generators that bind it (docs/naf.md).  Its
  argument's *quantified* variables (a nested `thereExists`) are **not** among the
  ones that must be bound — that is the whole point of the quantifier — so the pinning
  and closure logic reads `free-vars`, not every variable.  `thereExists` is
  deliberately **absent**: a *standalone* positive `(thereExists ?x S)` antecedent is
  desugared to `S` with `?x` a local generator variable (see the constructor), so it
  never reaches the chainers as its own literal; only `unknown` does.

  The **quantity comparisons** (`sameQuantity` / `quantityLessThan` /
  `quantityGreaterThan` / `quantityLessThanOrEqual` / `quantityGreaterThanOrEqual`) are
  deferred for the `evaluate` reason: `QuantityProver` (`vaelii.impl.provers`) *computes*
  them from two ground measure terms, so a comparison sorted ahead of the literal that
  binds its measure variable is inapplicable and the rule silently stops firing —
  pinning it after its binders is what a rule antecedent like
  `(quantityGreaterThan ?q (QuantityFn 100 Kilogram))`, whose `?q` a `(mass ?o ?q)`
  produces, needs.  Like `different`, being deferred is *all* they share with the
  arithmetic comparisons: they are absent from `comparison-siblings` and
  `chained-comparisons` above.  `sameQuantity` is symmetric, not directional, so it
  folds onto no `<` sibling; and while `quantityLessThan` is transitive, a measure chain
  crosses units, so collapsing `(quantityLessThan a b)` + `(quantityLessThan b c)` into
  one variable-arity literal would smuggle in a normalization the prover has not run —
  the same over-eager analogy the `different` note warns against.

  The **aggregates** are deferred for the sharpest version of the reason: an
  `(agg/count ?n ?v (ancestorOf ?v ?x))` is a census taken *of a group*, and which
  group is decided by `?x`, so running it before a generator binds `?x` would count the
  whole relation instead of one node's share.  Pinning it after its binders is also
  where GROUP BY comes from — the aggregate runs once per binding of the variables the
  generators supply, and yields one `?n` each (docs/aggregate.md)."
  (into '#{evaluate lessThan greaterThan different unknown
           sameQuantity quantityLessThan quantityGreaterThan
           quantityLessThanOrEqual quantityGreaterThanOrEqual}
        (keys aggregate-functors)))

(defn deferred-literal?
  "Is this literal one of the deferred (evaluable) ones?  Public because the storage
  canonicalization here and the query planner (`vaelii.impl.plan`) must hold back
  exactly the same set — if the two ever disagreed, a planner could hoist an
  `evaluate` above the literal binding its arguments, which yields no solutions
  rather than an error."
  [l]
  (and (sequential? l) (seq l) (contains? deferred-predicates (first l))))

;; ---- negation as failure: `unknown` and `thereExists` --------------------
;; `(unknown S)` is closed-world negation: it holds exactly while `S` is *not*
;; derivable.  `(thereExists ?x S)` existentially quantifies `?x` (or a vector of
;; variables), so it *closes* those variables off — a query with no free `?x` — which
;; is what lets `(unknown (thereExists ?x S))` express "there is no `x` such that S".
;; Both are answered by a prover (`vaelii.impl.provers`); nothing about either is
;; stored.  See docs/naf.md.

(def unknown-functor 'unknown)
(def there-exists-functor 'thereExists)

(defn unknown?
  "Is `form` an `(unknown S)` NAF literal?"
  [form]
  (and (sequential? form) (= unknown-functor (first form)) (= 2 (count form))))

(defn there-exists?
  "Is `form` a `(thereExists <var-or-vars> S)` existential?"
  [form]
  (and (sequential? form) (= there-exists-functor (first form)) (= 3 (count form))))

(defn naf-query-conjuncts
  "The conjunct literals an `(unknown …)` antecedent's query is evaluated as — the
  inner `(and …)` unwrapped, a single literal as a one-element vector.  The `unknown`
  spelling of `exception-query-conjuncts`, and the same reading: `unknown` is
  `exceptWhen` inlined per literal, so its query is a closed conjunction evaluated
  block-if-**all**-hold, and one evaluator (`provers/exception-holds?`) answers both.

  Closure is what makes the flat reading correct: every variable is bound before the
  query runs (`check-naf-closed`), so the conjuncts share nothing after substitution
  and each is an independent ground existence check.  A conjunction under a
  *quantifier* would not be — that is a join, and `check-naf-closed` refuses it.

  **Flattened all the way down**, because a nested `and` is not a goal any prover
  claims: left as one conjunct it would be handed to the registry, come back
  unanswerable, and read as *not derivable* — so the whole conjunction would never hold
  and the antecedent would guard nothing.  Conjunction is associative, so flattening is
  the reading rather than a normalization of it."
  [unk]
  (letfn [(flat [q]
            (if (and (sequential? q) (= and-functor (first q)))
              (mapcat flat (rest q))
              [q]))]
    (vec (flat (second unk)))))

(defn quantified-vars
  "The variables a `thereExists` binder introduces, as a set — its second element is a
  single variable or a *sequence* of them.  A written vector `[?x ?y]` is accepted, but
  so is the list `(?x ?y)` it becomes once `canon` / variable numbering / goal rewriting
  have normalized every sequential to a `PersistentList` — so this must not key on
  `vector?`, or a binder would silently stop binding the moment the form was
  canonicalized.  Non-variables are dropped (a malformed binder binds nothing), which
  makes `free-vars` treat a bad quantifier as vacuous rather than throwing during a
  pure construction; the well-formedness check refuses it separately."
  [form]
  (let [q (second form)]
    (cond
      (variable? q)   #{q}
      (sequential? q) (into #{} (filter variable?) q)
      :else           #{})))

;; ---- head existential: an existential variable in a rule consequent -------
;; `(exists <var-or-vars> C)` on a rule head marks a consequent variable that no
;; antecedent binds.  Range restriction (`rules/range-problems`) permits exactly the
;; marked variable — every *other* consequent variable must still be antecedent-bound —
;; and forward firing skolemizes it to a deterministic constant
;; (`vaelii.impl.skolem/skolemize-conclusion`).  The wrapper is stripped in the constructor: the stored
;; consequent is the inner `C`, so the existential variable survives as an ordinary
;; unbound consequent variable, which is exactly what firing re-derives it from.  See
;; docs/skolem.md.

(def exists-functor 'exists)

(defn head-exists?
  "Is `form` a head existential `(exists <var-or-vars> C)`?"
  [form]
  (and (sequential? form) (= exists-functor (first form)) (= 3 (count form))))

(defn head-exists-vars
  "The existential variables a head `(exists <vars> C)` introduces, as a set —
  a single variable or a sequence of them (`quantified-vars` reads either shape)."
  [form] (quantified-vars form))

(defn head-exists-body
  "The consequent `C` inside a head `(exists <vars> C)`."
  [form] (nth form 2))

(defn free-vars
  "The variables of `form` that must be **bound** before it can be evaluated — every
  variable it mentions, *minus* any bound by a `thereExists` quantifier within it.
  `unknown` is transparent (it binds nothing), a `thereExists` subtracts its binder,
  and every other form contributes all of its variables.  This is what the closure
  check and the planner read for a NAF literal instead of the raw variable set: the
  point of `(unknown (thereExists ?x (parentOf ?x Tom)))` is that `?x` is *not* one
  of the variables an antecedent has to supply."
  [form]
  (cond
    (unknown? form)      (free-vars (second form))
    (there-exists? form) (into #{} (remove (quantified-vars form)) (free-vars (nth form 2)))
    ;; an aggregate subtracts **both** of its own slots: `?v` is projected out (the
    ;; quantifier reading, as for `thereExists`) and `?n` is the operator's *output*,
    ;; so neither is a variable an earlier antecedent has to supply
    (aggregate? form)    (disj (into #{} (free-vars (aggregate-body form)))
                               (aggregate-value-var form)
                               (when (variable? (second form)) (second form)))
    (variable? form)     #{form}
    (sequential? form)   (into #{} (mapcat free-vars) form)
    :else                #{}))

(defn- var-occurrences
  "Every variable occurrence in `form`, with duplicates — so a variable used twice
  inside one literal counts twice.  Locality reads occurrence counts to tell 'only
  here' from 'here and elsewhere'."
  [form]
  (filter variable? (tree-seq sequential? seq form)))

;; ---- what a deferred literal reads, and what it writes -------------------
;; A deferred literal is *computed*, so unlike a matched one it has a direction: some
;; of its arguments are inputs it needs bound and the rest are outputs it fills in.
;; Three consumers need that split and must not each guess at it — the closure check
;; below (which refuses a literal nothing can bind), the forward chainer's post-join
;; phase (`rules/post-join-literals`), and the join's own guard.

(def ^:private deferred-output-arity
  "How many *leading* arguments of a deferred literal the computation writes rather
  than reads.  `(evaluate ?sum (+ 1 2))` fills in its first argument from the rest, and
  an aggregate fills in its `?n`; every other deferred predicate is a pure test, so it
  reads all of them."
  (into '{evaluate 1} (map (fn [f] [f 1])) (keys aggregate-functors)))

(defn deferred-output-vars
  "The variables a deferred literal **binds** — `evaluate`'s first argument, an
  aggregate's `?n`, and nothing at all for a pure test like `lessThan` or `different`."
  [g]
  (if (sequential? g)
    (into #{} (mapcat form-vars) (take (get deferred-output-arity (first g) 0) (rest g)))
    #{}))

(defn deferred-input-vars
  "The variables a deferred literal must have bound before it can run.

  `unknown` and the aggregates read `free-vars`, which already knows to subtract a
  quantifier's own binder — an aggregate's `?v` is projected out and its `?n` is
  written, so neither is an input.  Everything else reads every argument it does not
  write."
  [g]
  (cond
    (not (sequential? g))            #{}
    (or (unknown? g) (aggregate? g)) (free-vars g)
    :else (into #{} (mapcat form-vars) (drop (get deferred-output-arity (first g) 0) (rest g)))))

(defn there-exists-antecedent?
  "A *standalone* positive `thereExists` antecedent — one not wrapped in `unknown`.
  These desugar to their body (the quantifier's variable becoming a local matched
  variable); a `thereExists` *inside* an `unknown` is left intact for the NAF prover."
  [form]
  (there-exists? form))

(defn desugar-there-exists
  "Rewrite a rule's antecedent list, replacing every standalone positive `(thereExists
  ?x S)` with its body `S`.  A standalone existential antecedent is exactly `S` with
  `?x` a fresh local variable that the match binds and that (by locality) reaches
  nothing else — so `S` alone is the faithful, native reading, and it needs no special
  matcher: it joins the store like any generator, one witness per solution.  A
  `thereExists` under `unknown` is a NAF query, evaluated by the prover, and is not
  touched here."
  [antes]
  (mapv (fn [a] (if (there-exists-antecedent? a) (nth a 2) a)) antes))

(defn check-naf-closed
  "Throw unless a rule's negation-as-failure antecedents are usable — the mirror of
  `check-exception-closed`, pointed at `unknown` / `thereExists`:

  * **`unknown` is closed.**  Every free variable of an `(unknown S)` antecedent (the
    ones a nested `thereExists` does not bind) is bound by a *generator* antecedent —
    a positive literal that produces bindings, which a standalone `thereExists` becomes
    once desugared, but which `unknown` and the evaluables never are.  `unknown`
    produces no bindings and consumes them, so reaching one before its inputs exist
    tests an open sentence and silently yields nothing; forbidding it makes the
    mistake a legible error instead.
  * **Every quantifier is local.**  A `thereExists` bound variable appears *nowhere*
    in the rule outside its own `thereExists` literal, so it cannot leak into the
    consequent (a range-restriction hole) or capture another literal's variable (a
    silent misjoin).  Both read as working code, so both are refused here.
  * **An aggregate is closed and its reduction variable is local.**  Same two rules,
    for the same two reasons: `(agg/count ?n ?v (ancestorOf ?v ?x))` groups by
    `?x`, so `?x` must be bound or the census is of the whole relation, and
    `?v` is projected out, so a `?v` in the consequent would be a range-restriction
    hole that `range-problems` cannot see (it reads occurrences, and `?v` occurs).
  * **The reduction slot holds a variable.**  `(agg/count ?n Ada Body)` reduces over
    nothing — no prover claims it, so the rule stores and can never fire, which is the
    one outcome worse than an error.
  * **Every deferred literal's inputs are bound.**  A computed literal reaching the
    join without them cannot be answered *or* refuted, and the chainer throws rather
    than reporting a comparison that never ran as one that failed — mid-fixpoint,
    where a throw is exactly what the derivation path must not do.  So the rule is
    refused here, before anything is stored.

  **What counts as bound** is a generator antecedent's variables *plus* what the
  deferred literals themselves write: an aggregate's `?n` and an `evaluate`'s output.
  That is what lets a count be compared (`(and (person ?x) (agg/count ?n ?c (childOf
  ?x ?c)) (lessThan 2 ?n))`) — the reading that made aggregation worth having, and one
  the generator-only rule refused by counting the aggregate as a consumer only.

  A written output binds only the literals written **after** it, because that is the
  order every chainer runs them in: canonical order holds a deferred literal in the
  author's position, so `(and (evaluate ?z (+ ?q 1)) (evaluate ?q (+ 1 1)))` is refused
  and always was.  An aggregate is no exception — reordering the placement phase so a
  comparison could sit above its own count is something the forward chainer could do
  and the backward one could not, and two chainers disagreeing about one rule is worse
  than asking for the obvious writing order."
  [antes conseq exc]
  (let [scope    (vec (concat antes [conseq] exc))
        rule-occ (frequencies (var-occurrences scope))
        ;; a generator is a positive literal that *produces* bindings by matching —
        ;; which the deferred literals (aggregates and `unknown` among them) never do
        generators (remove #(or (unknown? %) (deferred-literal? %)) antes)
        matched    (into #{} (mapcat var-occurrences) generators)
        local-check
        (fn [lit vars kind]
          (let [local (frequencies (var-occurrences lit))]
            (when-let [leaked (seq (filter #(> (get rule-occ % 0) (get local % 0)) vars))]
              (throw (ex-info (str (clojure.core/name kind) " variable " (pr-str (vec leaked))
                                   " escapes its quantifier — a bound existential"
                                   " variable must appear only inside its own "
                                   (clojure.core/name kind))
                              {:type :quantifier-not-local :leaked (vec leaked)
                               kind lit :antecedents (vec antes)})))))
        closed-check
        (fn [lit bound kind]
          (when-let [loose (seq (remove bound (deferred-input-vars lit)))]
            (throw (ex-info (str (clojure.core/name kind) " antecedent is not closed: "
                                 (pr-str (vec loose))
                                 " unbound by anything else in the rule — it"
                                 " consumes bindings rather than producing them, so its"
                                 " inputs must be bound first")
                            {:type :naf-not-closed :unbound (vec loose)
                             kind lit :antecedents (vec antes)}))))
        quantified-body-check
        ;; A conjunction is legal where every conjunct is *closed*, because closure is
        ;; what makes it a set of independent ground checks rather than a join — and
        ;; the level-6 registry, which answers one goal at a time, has no join.  Under a
        ;; quantifier the conjuncts share the binder, so the flat reading would answer
        ;; each from a different witness: "has a sick child" would hold of anyone with a
        ;; child while anyone at all is sick.  Refused here rather than mis-evaluated.
        (fn [lit body kind]
          (when (and (sequential? body) (= and-functor (first body)))
            (throw (ex-info (str (clojure.core/name kind) " quantifies a conjunction,"
                                 " which needs a join to answer: its conjuncts share the"
                                 " bound variable, and each is evaluated on its own."
                                 "  Bind the witness with a generator antecedent instead")
                            {:type :quantified-conjunction kind lit
                             :antecedents (vec antes)}))))]
    ;; locality: each thereExists / aggregate binder occurs only within its own literal
    (doseq [te (filter there-exists? (tree-seq sequential? seq scope))]
      (local-check te (quantified-vars te) :thereExists)
      (quantified-body-check te (nth te 2) :thereExists))
    (doseq [ag (filter aggregate? (tree-seq sequential? seq scope))]
      (quantified-body-check ag (aggregate-body ag) :aggregate)
      (if-let [v (aggregate-value-var ag)]
        (local-check ag #{v} :aggregate)
        (throw (ex-info (str "aggregate reduces over " (pr-str (nth ag 2))
                             ", which is not a variable — the second slot names the"
                             " value being reduced, so a constant there reduces over"
                             " nothing and no prover can answer it")
                        {:type :not-well-formed :aggregate ag
                         :antecedents (vec antes)}))))
    ;; an `unknown`'s conjunction is real, and empty is not one of its shapes
    (doseq [unk (filter unknown? antes)]
      (when (empty? (naf-query-conjuncts unk))
        (throw (ex-info (str "unknown antecedent " (pr-str unk) " queries an empty"
                             " conjunction, which nothing can make derivable — so the"
                             " unknown always holds and the antecedent guards nothing")
                        {:type :not-well-formed :unknown unk
                         :antecedents (vec antes)}))))
    ;; closure: every consuming literal's inputs are bound by the generators or by a
    ;; deferred literal written before it — so the scan is left to right, accumulating
    ;; each literal's outputs only once it has been passed
    (reduce (fn [bound a]
              (if (or (unknown? a) (deferred-literal? a))
                (do (closed-check a bound (cond (unknown? a)   :unknown
                                                (aggregate? a) :aggregate
                                                :else          :deferred))
                    (into bound (deferred-output-vars a)))
                bound))
            matched
            antes)
    nil))

(defn- fold-comparison
  "Fold a comparison onto its canonical sibling by reversing the arguments —
  (greaterThan a b c) ⇒ (lessThan c b a).  A dotted-rest form is left alone: its
  arguments are a splice, not a positional list."
  [form]
  (if-let [sib (and (sequential? form) (seq form)
                    (not-any? #(= dot-marker %) form)
                    (comparison-siblings (first form)))]
    (apply list sib (reverse (rest form)))
    form))

;; ---- structural term order (lexical only as the last resort) -------------

(defn- canonical-var-index
  "The N of a canonical variable ?varN, or nil for any other variable."
  [x]
  (when (variable? x)
    ;; hinted for `variable?`'s reason, one screen up: this is the file's other
    ;; `name`-then-interop pair, and it reflects under the same rewriter
    (let [^String n (clojure.core/name x)]
      (when (.startsWith n "?var")
        (try (Long/parseLong (subs n 4)) (catch Exception _ nil))))))

(defn- term-rank
  "Coarse structural class, compared before any value: numbers < strings <
  constants < compounds < variables.  Variables sort last so the more informative
  (ground) parts of a literal drive the order."
  [t]
  (cond (variable? t)   4
        (sequential? t) 3
        (number? t)     0
        (string? t)     1
        :else           2))

;; Genuine in-file cycle, and the shape of the data: `cmp-term` on a compound descends to
;; `cmp-seq`, which compares element-for-element with `cmp-term`.  Terms nest arbitrarily,
;; so no ordering of the two removes it.
(declare cmp-term)

(defn- cmp-seq [a b]
  (let [c (compare (count a) (count b))]
    (if-not (zero? c)
      c
      (or (first (remove zero? (map cmp-term a b))) 0))))

(defn- cmp-term
  "Total order on terms, structural first: rank, then arity/shape, then value.
  Variables compare by their canonical *index* (numeric) and are otherwise
  indistinguishable — never compared by name.  A lexical comparison of constant
  symbols/strings is the last resort."
  [a b]
  (let [ra (term-rank a) rb (term-rank b)]
    (cond
      (not= ra rb)    (compare ra rb)
      (variable? a)   (let [ia (canonical-var-index a) ib (canonical-var-index b)]
                        (if (and ia ib) (compare ia ib) 0))   ; unnumbered vars tie
      (number? a)     (compare a b)
      (sequential? a) (cmp-seq a b)
      :else           (compare (str a) (str b)))))            ; last resort: lexical

(defn- cmp-blind
  "Structural comparison that is **blind to variables**: any two variables are
  interchangeable.  Used to form tie groups *before* canonical numbering exists, so
  the pre-numbering order can never depend on the author's variable names (and is a
  proper equivalence, hence a transitive comparator)."
  [a b]
  (let [ra (term-rank a) rb (term-rank b)]
    (cond
      (not= ra rb)    (compare ra rb)
      (variable? a)   0
      (number? a)     (compare a b)
      (sequential? a) (let [c (compare (count a) (count b))]
                        (if (zero? c)
                          (or (first (remove zero? (map cmp-blind a b))) 0)
                          c))
      :else           (compare (str a) (str b)))))

(defn- cmp-literals
  "Compare two literal *sequences* elementwise (used to pick the minimal candidate
  ordering once every variable is canonically numbered)."
  [xs ys]
  (or (first (remove zero? (map cmp-term xs ys))) 0))

(defn- cmp-render
  "Compare two fully rendered candidates `[antecedents consequent _varmap]`.
  The **whole** rule decides, not just its antecedents: two orderings of a tie group
  can produce the identical numbered antecedent vector and still differ in what the
  consequent says about those numbers, and picking between them by arrival order is
  exactly the leak canonicalization exists to close.  A disconnected self-join is the
  two-literal case — `(implies (and (p ?a ?b) (p ?c ?d)) (q ?a ?c))` renders
  `(q ?var0 ?var2)` one way round and `(q ?var2 ?var0)` the other, and they are the
  same rule."
  [[l1 c1] [l2 c2]]
  (let [a (cmp-literals l1 l2)]
    (if-not (zero? a) a (cmp-term c1 c2))))

(defn sort-conjuncts
  "Put a conjunction of literals into canonical order and drop duplicates, using the
  same structural comparator the rule canonicalizer uses.  An exceptWhen exception's
  conjuncts are independent ground checks, so their written order (and a repeat) is not
  their identity — sorting makes two spellings of one exception the same meta-sentex."
  [literals]
  (vec (distinct (sort cmp-term literals))))

;; ---- tail projection: fold the tail into the antecedent search -----------

(def ^:private unnumbered-sentinel
  "A canonical variable whose index is beyond any a real rule reaches, so `cmp-term`
  sorts it after every genuinely numbered variable.  A not-yet-numbered variable is
  projected to it — a placeholder that says only 'this will be some *larger* number'."
  (intern-sym (symbol (str "?var" Long/MAX_VALUE))))

(defn- project-form
  "`form` with every variable replaced by its canonical number from `m` (author-var →
  ?varN), or `unnumbered-sentinel` where `m` has not numbered it yet.  The rendering a
  survivor's partial numbering already fixes for a downstream form, used to rank
  survivors whose antecedent prefix ties."
  [m form]
  (cond
    (variable? form)   (get m form unnumbered-sentinel)
    (sequential? form) (apply list (map #(project-form m %) form))
    :else              form))

;; ---- symmetric arguments -------------------------------------------------

(defn ground-term?
  "True when `t` contains no pattern variable anywhere."
  [t]
  (not-any? variable? (tree-seq sequential? seq t)))

(defn symmetric-literal?
  "A binary literal whose predicate is declared symmetric (and not a dotted form)."
  [form symmetric?]
  (boolean (and (sequential? form) (= 3 (count form)) (symbol? (first form))
                (not-any? #(= dot-marker %) form)
                (symmetric? (first form)))))

(defn- sort-symmetric-args
  "Sort the arguments of a **fully ground** binary literal whose predicate is declared
  symmetric, so (siblingOf Bob Ann) and (siblingOf Ann Bob) store as one sentex.

  Only ground literals are reordered.  A literal holding a variable is a *pattern* —
  a query, or a rule antecedent about to be matched — and variables sort last, so
  sorting one would move its ground argument into slot 1 and make it miss the stored
  fact.  Order-insensitive *lookup* is handled at match time instead
  (`res/raw-match` tries both argument orders for a symmetric predicate)."
  [form symmetric?]
  (if (and (symmetric-literal? form symmetric?)
           (every? ground-term? (rest form)))
    (let [[p x y] form]
      (if (pos? (cmp-term x y)) (list p y x) form))
    form))

(defn mirror-literal
  "The argument-swapped twin of a binary literal, for symmetric lookup."
  [form]
  (let [[p x y] form] (list p y x)))

(defn- sort-naf-conjuncts
  "Put the conjuncts of an `(unknown (and …))` antecedent into canonical order and drop
  repeats, so two spellings of one NAF condition are one rule.  The same claim
  `sort-conjuncts` makes for an exceptWhen exception, and for the same reason: the
  conjuncts are independent ground checks, so their written order is not their
  identity.

  Sorted **blind to variables**, unlike the exception's — an exception's conjuncts are
  aligned to the rule's canonical varmap before they are sorted (`vaelii.core`), while
  this runs on the surface literal, where the author's variable names are still what
  they wrote.

  Nesting goes with the order: `naf-query-conjuncts` flattens, so a nested spelling and
  the flat one store as the same rule, and a lone conjunct loses the `and` it never
  needed.  An empty conjunction is left exactly as written for `check-naf-closed` to
  refuse — rewriting it here would erase the shape the diagnostic names."
  [form]
  (if (and (unknown? form) (sequential? (second form))
           (= and-functor (first (second form))))
    (let [cs (vec (distinct (sort cmp-blind (naf-query-conjuncts form))))]
      (cond
        (empty? cs)      form
        (= 1 (count cs)) (list unknown-functor (first cs))
        :else            (list unknown-functor (apply list and-functor cs))))
    form))

(defn- normalize-literal [form symmetric?]
  (-> form fold-comparison sort-naf-conjuncts (sort-symmetric-args symmetric?)))

;; ---- chained comparisons collapse into one variable-arity literal -------

(defn- collapse-comparison-chains
  "Merge chained comparisons among `lits` into single variable-arity literals:
  (lessThan a b) + (lessThan b c) ⇒ (lessThan a b c).  Only a simple chain merges —
  a branch (a<b, a<c) is left alone."
  [lits]
  (let [chain? #(and (sequential? %) (contains? chained-comparisons (first %))
                     (>= (count %) 3) (not-any? (fn [t] (= dot-marker t)) %))
        chains (filterv chain? lits)
        others (filterv (complement chain?) lits)]
    (if (< (count chains) 2)
      (vec lits)
      (let [merged (loop [cs (mapv vec chains)]
                     (if-let [[i j] (first (for [i (range (count cs))
                                                 j (range (count cs))
                                                 :when (and (not= i j)
                                                            (= (last (nth cs i))
                                                               (second (nth cs j))))]
                                             [i j]))]
                       (let [joined  (into (nth cs i) (drop 2 (nth cs j)))
                             rest-cs (keep-indexed (fn [k v] (when-not (#{i j} k) v)) cs)]
                         (recur (vec (cons joined rest-cs))))
                       cs))]
        (into others (map #(apply list %)) merged)))))

;; ---- canonical variables -------------------------------------------------

(def ^:private empty-numbering
  "A fresh canonical-variable numbering: `:n` the next index, `:m` the author's
  variable → its canonical name, `:vm` the inverse (the `:varmap` a sentex carries)."
  {:n 0 :m {} :vm {}})

(defn- number-form
  "Number every variable in `form` to ?var0, ?var1, … by first occurrence, continuing
  the numbering `st`.  Each anonymous `_` gets its own fresh, unshared name (two
  occurrences are two different variables).  Returns [numbered-form st']."
  [st form]
  (let [state (volatile! st)
        fresh (fn [orig]
                (let [{:keys [n vm]} @state
                      v (intern-sym (symbol (str "?var" n)))]
                  (vswap! state assoc :n (inc n) :vm (assoc vm v orig))
                  v))]
    (letfn [(rn [x]
              (cond
                (and (symbol? x) (= "_" (clojure.core/name x))) (fresh x)
                (variable? x) (or (get (:m @state) x)
                                  (let [v (fresh x)]
                                    (vswap! state update :m assoc x v)
                                    v))
                (sequential? x) (apply list (map rn x))
                :else x))]
      (let [r (rn form)] [r @state]))))

(defn- number-forms
  "Number a sequence of forms in order under one shared numbering."
  [st forms]
  (reduce (fn [[acc s] f] (let [[r s'] (number-form s f)] [(conj acc r) s']))
          [[] st] forms))

(defn- tie-groups
  "Split a `cmp-blind`-sorted literal vector into maximal runs of mutually tied
  literals — the literals whose relative order structure alone cannot decide."
  [sorted]
  (reduce (fn [groups l]
            (if (and (seq groups) (zero? (cmp-blind (first (peek groups)) l)))
              (conj (pop groups) (conj (peek groups) l))
              (conj groups [l])))
          [] sorted))

(defn- extend-minimally
  "Extend every partial order in `states` by one literal drawn from its own remaining
  pool, keeping only the extensions whose *canonically numbered* literal is smallest.
  A state is `{:order [numbered-literal …] :st <numbering> :left [author-literal …]}`."
  [states]
  (let [exts (vec (for [{:keys [order st left] :as s} states
                        i (range (count left))
                        :let [[r st'] (number-form st (nth left i))]]
                    [r (assoc s :order (conj order r)         ; assoc, not a fresh map, so a
                              :st st'                          ; carried tag (:origin) survives
                              :left (into (subvec left 0 i) (subvec left (inc i))))]))
        best (reduce (fn [a b] (if (neg? (cmp-term (first b) (first a))) b a)) exts)]
    (into [] (comp (filter #(zero? (cmp-term (first %) (first best))))
                   (map second)
                   (distinct))
          exts)))

(defn- suffix-vars
  "For each tie group, the author variables that still occur *after* it — in the later
  groups and in `tail-forms` (the held-back literals, the consequent, the exception).
  Two survivors that agree on those are interchangeable from there on, whatever they
  did with the variables nobody mentions again, so this is what collapses the
  survivor set between groups."
  [groups tail-forms]
  (let [base (into #{} (mapcat form-vars) tail-forms)
        acc  (reduce (fn [a g] (conj a (into (peek a) (mapcat form-vars) g)))
                     [base] (reverse groups))]
    (vec (reverse (subvec acc 0 (count groups))))))

(defn- prune-survivors
  "Drop survivors that can no longer be told apart: same numbered prefix, same next
  index, same numbering of every variable that occurs again."
  [states relevant]
  (:out (reduce (fn [{:keys [seen out] :as acc} s]
                  (let [k [(:order s) (:n (:st s)) (select-keys (:m (:st s)) relevant)]]
                    (if (contains? seen k) acc {:seen (conj seen k) :out (conj out s)})))
                {:seen #{} :out []} states)))

(defn- literal-var-sets [g] (map #(into #{} (form-vars %)) g))

(defn- pruneable-groups
  "For each tie group, whether `prune-by-tail` may bound it.  Two conditions, both
  needed for the tail projection to be exact *and* independent of author order:

    * **joinless** — no variable occurs in two of the group's literals, so every
      ordering renders the identical antecedent block (the automorphic case); the only
      thing an ordering changes is what the consequent says about it.
    * **tail-isolated** — none of the group's variables occurs in any *other*
      antecedent (another group, or a held-back literal), so its ordering cannot move
      any antecedent but its own.  The consequent is then the whole tiebreak, and it is
      a never-reordered form — so projecting it is a function of the rule's content,
      not of the order it was written in.

  A group that fails either stays on the exact `extend-minimally` search, whose
  antecedent minimization already collapses a join to O(k²)."
  [groups defs]
  (let [gvars (mapv #(into #{} (mapcat form-vars) %) groups)
        else  (fn [i] (reduce into (into #{} (mapcat form-vars) defs)
                              (keep-indexed (fn [j vs] (when (not= i j) vs)) gvars)))
        joinless? (fn [g] (let [vs (mapcat seq (literal-var-sets g))]
                            (or (empty? vs) (apply distinct? vs))))]
    (mapv (fn [i g] (and (or (<= (count g) 1) (joinless? g))
                         (not-any? (else i) (nth gvars i))))
          (range (count groups)) groups)))

(defn- prune-by-tail
  "Break an antecedent tie by the tail, for a joinless, tail-isolated group (see
  `pruneable-groups`).  Every ordering of such a group renders the identical
  antecedents, so `cmp-render` decides between them purely on `proj-forms` — the
  consequent.  Project it under each survivor's partial numbering (an unnumbered
  variable → a sentinel that sorts last), keep only the survivors whose projection is
  minimal, and collapse any left interchangeable on the projected variables.

  This is what makes the automorphic case tractable without a cap.  k interchangeable
  antecedents that a consequent numbers differently render the same antecedents but a
  different consequent, so the exact search keeps all k! orderings and picks the
  minimal consequent only at the end.  Projecting it *during* the search keeps only the
  minimal-so-far survivors each round — O(k²) states, not k!.  It is exact, not a
  heuristic: numbering is monotonic across rounds (round r assigns larger numbers than
  round r-1), so a still-unnumbered variable can only be given a *larger* number than
  one already placed.  A survivor whose projection is strictly larger at the first
  differing position is therefore strictly larger in the final rendering too, and can
  never be the whole-rule minimum — dropping it discards no candidate the end-stage
  `cmp-render` would have chosen.

  Two sets, not one.  `keep-min` *ranks* survivors by `proj-forms` (the tail), grouped
  by `[:origin :order]` — the tail is the true tiebreak only among survivors that render
  the same antecedents *and* descend from the same incoming survivor (`:origin`), since
  those alone are antecedent-equal for good (a joinless, tail-isolated group changes no
  antecedent but its own).  Two survivors from *different* origins differ on an earlier
  group's antecedents, which outrank the tail, so `keep-min` never compares them.  The
  dedup then *merges* only survivors interchangeable on `relevant` — every variable that
  recurs downstream (later groups and the tail), the set `prune-survivors` uses — never
  on the tail alone: two survivors can render the tail identically yet still differ on a
  variable a later group needs, and merging them there would drop a distinct rule."
  [states proj-forms relevant]
  (let [keep-min (fn [grp]
                   (let [projed (mapv (fn [s] [(mapv #(project-form (:m (:st s)) %) proj-forms) s])
                                      grp)
                         best   (reduce (fn [a b] (if (neg? (cmp-literals (first b) (first a))) b a))
                                        projed)
                         bp     (first best)]
                     (into [] (comp (filter #(zero? (cmp-literals (first %) bp))) (map second))
                           projed)))]
    (:out (reduce (fn [{:keys [seen out] :as acc} s]
                    (let [k [(:order s) (:n (:st s)) (select-keys (:m (:st s)) relevant)]]
                      (if (contains? seen k) acc {:seen (conj seen k) :out (conj out s)})))
                  {:seen #{} :out []}
                  (mapcat keep-min (vals (group-by (juxt :origin :order) states)))))))

(defn- minimal-orders
  "Every ordering of the tie `groups` whose canonically-numbered literal vector is
  lexicographically minimal — the candidates the whole-rule tie-break then chooses
  between.  `tail-forms` are the forms numbered after the generators (the held-back
  literals, then the consequent); they decide which survivors still differ.

  This is prefix minimization, not enumeration.  The numbering of a prefix depends
  only on that prefix, and `cmp-literals` is lexicographic over the literal vector,
  so a globally minimal order has a minimal prefix at every step: extending only the
  minimal prefixes is *exact*.  It is also what makes the cost structural rather than
  combinatorial — a tie group whose literals are distinguishable at all collapses to
  one survivor as soon as the first pick numbers a shared variable (a join chain does
  it immediately), so k literals cost O(k²) numberings rather than k!.

  The remaining hard shape is genuine **automorphism**: k antecedents of one predicate
  sharing no variable with each other are a cross product, so every ordering renders
  the same antecedents and the tie falls entirely to what the consequent says about
  them.  A group that is joinless and tail-isolated (`pruneable-groups`) is bounded by
  `prune-by-tail`, which folds the consequent/exception into the search and keeps only
  the survivors whose projected tail is minimal each round — so the automorphic case
  stays O(k²) too rather than enumerating k!.  Every reduction is exact (see
  `extend-minimally` and `prune-by-tail`), so the search has no cutoff.  `defs` are the
  held-back literals and `proj-forms` the consequent then exception."
  [groups tail-forms defs proj-forms]
  (if (every? #(= 1 (count %)) groups)
    ;; nothing tied: one ordering, numbered straight through.  This is the overwhelming
    ;; majority of rules, and it must not pay for the search.
    (let [[order st] (number-forms empty-numbering (map first groups))]
      [{:order order :st st}])
    ;; `after` / `eligible` are only consulted when a group ties, which a rule with any
    ;; structure at all never does — so they are computed on demand
    (let [after    (delay (suffix-vars groups tail-forms))
          eligible (delay (pruneable-groups groups defs))]
      (first
       (reduce (fn [[states i] g]
                 (let [relevant  (nth @after i)
                       eligible? (nth @eligible i)
                       ;; tag each incoming survivor with an origin, so `keep-min` breaks
                       ;; the group's tie by the consequent only *within* one origin (the
                       ;; survivors it is antecedent-equal to), never across the distinct
                       ;; antecedents earlier groups already committed to
                       init  (if eligible? (map-indexed #(assoc %2 :origin %1) states) states)
                       prune (if eligible? #(prune-by-tail % proj-forms relevant) identity)
                       ss (loop [ss (mapv #(assoc % :left (vec g)) init), k (count g)]
                            (if (zero? k)
                              ss
                              ;; prune each round, not just after the group: an automorphic
                              ;; group would reach k! survivors before the group finished
                              (recur (prune (extend-minimally ss)) (dec k))))
                       ss (mapv #(dissoc % :left :origin) ss)]
                   [(if (next ss) (prune-survivors ss relevant) ss) (inc i)]))
               [[{:order [] :st empty-numbering}] 0]
               groups)))))

(defn- framed-pred
  "The predicate a literal is *about*, descending the `not` and `ist` frames: `r` for
  `(r ?x)`, `(not (r ?x))` and `(ist ?c (r ?x))` alike.  This is the identity the
  recursive-literal hold-back keys on — a rule concluding `(not (anc ?x ?z))` recurses
  through an `anc` antecedent exactly as its positive twin does, and the frame is not
  the predicate.  Reading the frame itself as the predicate would classify every
  `not`-headed antecedent as recursive under a `not`-headed consequent, holding all of
  them in author order and losing the canonical sort."
  [form]
  (loop [f form]
    (cond
      (negation? f) (recur (second f))
      (and (sequential? f) (= ist-functor (first f)) (= 3 (count f))) (recur (nth f 2))
      (sequential? f) (first f)
      :else nil)))

(defn- canonicalize-rule
  "Canonical antecedent order + canonical variables for a rule.  Returns
  [antecedents consequent varmap].

  Only the *generator* literals are reordered.  Two kinds are held back, in the
  author's relative order, because their position is operational rather than
  logical: **deferred** (evaluable) literals, which consume bindings the generators
  produce, and the **recursive** literal of a recursive rule — reordering that one
  could turn an author's right-recursive rule left-recursive, which the backward
  chainers cannot execute (see `vaelii.impl.resolution`).

  Generators are sorted with the variable-blind comparator, so the pre-numbering
  order can never depend on the author's variable names.  Literals that tie under it
  (a same-predicate self-join, say) are resolved by searching the orderings of the
  tie group and keeping the one whose *canonically numbered* form is smallest — so
  the result is a function of the rule's structure, not of the order it was written
  in.  Smallest is judged on the **whole** rule (`cmp-render`): antecedents first,
  then the consequent, because two orderings can agree on the antecedents and
  disagree on what the consequent says about them.  The search is `minimal-orders`,
  which is exact and has no cutoff.

  An `exceptWhen` exception is not part of the rule and takes no part here: it is a
  separate meta-sentex whose variables are aligned to this rule's `varmap` when the
  exception is asserted (`vaelii.core`)."
  [antes conseq symmetric?]
  (let [norm       #(normalize-literal % symmetric?)
        all        (collapse-comparison-chains (mapv norm antes))
        conseq0    (norm conseq)
        conseq-pred (framed-pred conseq0)
        held?      (fn [l] (or (deferred-literal? l)
                               (and (some? conseq-pred)
                                    (= (framed-pred l) conseq-pred))))
        gens       (filterv (complement held?) all)
        defs       (filterv held? all)
        ;; the generators are numbered by the search; the held-back literals, then the
        ;; consequent continue that same numbering
        render     (fn [{:keys [order st]}]
                     (let [[dlits st1] (number-forms st defs)
                           [conseq' st2] (number-form st1 conseq0)]
                       [(into order dlits) conseq' (:vm st2)]))
        candidates (minimal-orders (tie-groups (vec (sort cmp-blind gens)))
                                   (conj defs conseq0)
                                   defs
                                   [conseq0])]
    (reduce (fn [best cand]
              (let [r (render cand)]
                (if (or (nil? best) (neg? (cmp-render r best))) r best)))
            nil candidates)))

(defn rule-sentence
  "Build the rule form from antecedent patterns + a consequent pattern — a single
  antecedent needs no `and`.  This is the spelling the constructor *stores* (it
  rebuilds the sentence from the canonical antecedents below), so it is the one
  builder: `rules/rule-sentence` delegates here, so a rule reaches the constructor
  in exactly one surface spelling rather than two that only canonicalization
  converges."
  [antes conseq]
  (list rule-functor
        (if (= 1 (count antes)) (first antes) (apply list and-functor antes))
        conseq))

;; ---- construction --------------------------------------------------------

(defn- constructed-sentex
  "The ordinary sentex construction: peel the direction / default / assumption / (surface)
  exceptWhen wrappers, then canonicalize a rule or a fact.  Split out of `sentex` so the
  exceptWhen meta-sentex short-circuit there reads cleanly."
  [sentence context symmetric?]
  (let [[dir def? _exc assum con inner0] (peel-rule-wrapper sentence)
        ctx              (intern-sym context)
        inner            (canon inner0)
        [truth body]     (peel-not inner)
        rule?            (implies? body)]
    (if rule?
      (let [antes0     (rule-antecedents body)
            conseq-raw (rule-consequent body)
            ;; a head existential `(exists ?y C)` stores as its inner `C`: the marked
            ;; variable survives as an ordinary unbound consequent variable that
            ;; forward firing skolemizes.  Range restriction already permitted it
            ;; (`rules/range-problems`, on the wrapped surface form).  See docs/skolem.md.
            conseq0    (if (head-exists? conseq-raw) (head-exists-body conseq-raw) conseq-raw)]
        ;; A surface `exceptWhen` wrapper (`_exc`) is stripped and dropped here: the
        ;; exception is not part of the rule and cannot be represented on the record.  The
        ;; assert layer splits it off first and stores it as a meta-sentex (`vaelii.core`),
        ;; so a pure construction of a wrapped rule stores the bare rule alone.  NAF
        ;; antecedents still must be closed and their `thereExists` quantifiers local
        ;; before canonicalization.
        (check-naf-closed antes0 conseq0 nil)
        (let [antes1 (desugar-there-exists antes0)      ; standalone thereExists -> body
              [antes conseq varmap]
              (canonicalize-rule antes1 conseq0 symmetric?)
              sent (rule-sentence antes conseq)]
          (->RuleSentex (if (= truth :false) (list not-functor sent) sent)
                        ctx nil truth antes conseq nil varmap
                        (or dir :both)                        ; a bare implies works both ways
                        def? assum con)))
      (let [b      (normalize-literal body symmetric?)
            stored (if (= truth :false) (list not-functor b) b)]
        ;; a wrapper on a non-rule is meaningless; it is stripped and ignored
        (->AtomicSentex stored ctx nil truth nil)))))

(defn sentex
  "Construct a sentex — an `AtomicSentex` or a `RuleSentex` — canonicalizing the structural
  connectives into the record and the sentence into canonical form (see the namespace
  docstring).  Context defaults to 'default; id defaults to nil until the record store
  assigns a handle.

  `opts` may carry `:symmetric?` — a predicate telling whether a functor is declared
  symmetric, so its arguments can be sorted.  Without it no predicate is treated as
  symmetric (a pure, KB-free construction)."
  ([sentence] (sentex sentence 'default))
  ([sentence context] (sentex sentence context nil))
  ([sentence context {:keys [symmetric?] :or {symmetric? (constantly false)}}]
   ;; A `(exceptWhen <query> (sentexHandle H))` meta-sentex is stored **verbatim** as an
   ;; Atomic — `peel-rule-wrapper` would otherwise strip the exceptWhen and drop the
   ;; query, since it cannot tell the stored meta form from the surface wrapper.  This is
   ;; the one point that can: the wrapper's second argument is a rule, the meta's is a
   ;; handle.  Its query holds the rule's canonical variables, so it is a non-ground
   ;; Atomic — exempt from the ground-fact check by the assert layer.
   (if (exceptWhen-meta? sentence)
     (->AtomicSentex (canon sentence) (intern-sym context) nil :true nil)
     (constructed-sentex sentence context symmetric?))))

(defn body
  "The positive atomic form a sentex asserts (a fact's sentence without its `not`);
  nil for a rule."
  [{:keys [sentence truth antecedent]}]
  (when-not (some? antecedent)
    (if (= truth :false) (second sentence) sentence)))

(defn positive-body
  "The double-negation-eliminated positive body of a sentence, or nil when the
  sentence is genuinely negative.  Constraint checks use this rather than the full
  canonical form: they must see the predicate and argument order the *author* wrote,
  not a folded sibling (`greaterThan` ⇒ `lessThan`) or sorted symmetric arguments,
  or an `argIsa` would be enforced against the wrong position."
  [sentence]
  (let [[truth body] (peel-not (canon sentence))]
    (when (= :true truth) body)))

(defn underlying-body
  "The body a sentence's `not` wrappers enclose, **whatever its polarity** — `S` for
  both `S` and `(not S)`.

  Its neighbour above answers the *constraint* question, where a genuinely negative
  sentence has no body to constrain and nil is the right answer.  This answers the
  *content* question: `(not (penguin X))` is content about `penguin`, so a trigger
  keyed on a predicate has to see it arrive and leave, and a re-check that only ever
  saw the positive polarity would miss every withdrawal a negation causes."
  [sentence]
  (second (peel-not (canon sentence))))

(defn- ist-read-problem
  "The refusal an `(ist Ctx S)` in antecedent or exception position carries.

  `ist` **places**: `assert` finds-or-creates S in Ctx, and a rule consequent names
  where its conclusion lands.  Nothing reads through it.  The literal is indexed and
  matched under the functor `ist` (`rules/antecedent-predicates`, `res/match-pattern`),
  which no sentex is ever stored with, so it satisfies nothing and no arriving datum
  triggers it.

  Which way that falls out depends on the frame, and **every** way is a rule deciding
  itself on a context it never read: a positive antecedent is never satisfied, so the
  rule cannot fire; an `exceptWhen` query never matches, so the guard never guards and
  the conclusion it was written to block stands believed; and an `(unknown (ist …))` is
  satisfied by the same emptiness, so the rule fires unconditionally.  The middle two
  are why this is refused rather than left inert — a rule that does nothing is visible,
  and a guard that passes everything is not.

  What such an author wants is for S to be **visible** where the rule is, and there are
  two ways to say that: `(decontextualizedPredicate P)` takes every `(P ...)` into
  CxUniverse, which every context sees, and a `genlCx` edge puts Ctx in the
  rule's own cone.  Under either the literal is written plainly, and belief no longer
  turns on a frame the matcher cannot honor."
  [role]
  (str "ist places a conclusion and reads nothing: an (ist Ctx S) "
       (clojure.core/name role) " matches no stored sentex, so it decides the rule"
       " without ever consulting Ctx — make S visible with (decontextualizedPredicate P)"
       " or a genlCx edge, and write S plainly"))

(defn connective-problems
  "Structural problems with `sentence`'s connective frames, as strings (empty if OK) —
  read by `check` and thrown by `assert` under `:not-well-formed` before anything is
  stored:

  * a structural connective at an arity it does not have — `(not A B)` would store as
    a positive fact whose record and index disagree about what it says, and an
    `implies` at arity 2 threw a bare exception where arity 4 silently dropped its
    tail;
  * a rule or exception literal that is not itself a sentence — a bare symbol in
    antecedent or consequent position matches nothing and checks as nothing;
  * a head existential outside consequent position — `exists` marks a consequent
    variable for skolemization and is not a predicate;
  * an `(ist Ctx S)` in antecedent or exception position — `ist` places and never
    reads, so the literal matches nothing (`ist-read-problem`);
  * a nested `implies` anywhere but a rule's consequent — a rule is a sentence, not a
    literal, and consequent position is the one place it means something else: a
    **generator**, whose firing stamps the inner rule out (docs/generators.md).  The
    nesting is not capped there: a stamped rule may stamp one in turn, and each level
    is checked in the ordinary rule roles;
  * a negated rule — `not` over an `implies`, bare or wrapped: negation lives on
    facts, and what a rule's negation would mean is said as an exception or a
    retraction instead (the record has no shape for it — a rule under `not` would
    store a sentence its own key cannot be computed from);
  * a top-level `and` — a conjunction is an antecedent or a query, never one
    assertable sentence; assert its conjuncts."
  [sentence]
  (letfn
   [(walk [role form]
      (cond
        (variable? form) []                        ; a pattern position; not ours
        (not (sequential? form))
        (if (= :sentence role)
          []                                       ; top-level shape has its own check
          [(str "a " (clojure.core/name role) " literal must be a sentence, got " (pr-str form))])
        (empty? form) ["an empty form is not a sentence"]
        :else
        (let [h (first form) n (count form)]
          (cond
            (variable? h)                 []       ; `(?p ?x)` names no connective
            (do-form? form)               []
            (= sentex-handle-functor h)   []
            (or (= h default-rule-wrapper) (= h assumption-rule-wrapper)
                (contains? rule-direction-wrappers h) (constraint-rule-wrappers h))
            (if (= 2 n)
              (walk role (second form))
              [(str (pr-str h) " wraps one rule, got arity " (dec n))])
            (= h except-wrapper)
            (if (= 3 n)
              (into (vec (mapcat #(walk :exception %)
                                 (exception-conjuncts (second form))))
                    (walk role (nth form 2)))
              [(str "exceptWhen takes a query and a rule, got arity " (dec n))])
            (= h not-functor)
            (cond
              (not= 2 n)
              [(str "not takes one sentence, got arity " (dec n))]
              (implies? (peek (peel-rule-wrapper (second form))))
              ["a rule cannot be negated; retract it, or state the exception the negation means"]
              :else (walk role (second form)))
            (= h ist-functor)
            (cond
              (contains? #{:antecedent :exception} role) [(ist-read-problem role)]
              (= 3 n)        (walk role (nth form 2))
              (= :sentence role) []  ; the top-level ist arity has its own `:shape` contract
              :else [(str "ist takes a context and a sentence, got arity " (dec n))])
            (= h and-functor)
            (if (= :sentence role)
              ["a conjunction is not one assertable sentence; assert its conjuncts"]
              (vec (mapcat #(walk role %) (rest form))))
            (= h rule-functor)
            (cond
              (not= 3 n)
              [(str "implies takes antecedents and one consequent, got arity " (dec n))]
              ;; A rule **in consequent position** is a generator's head: the rule its
              ;; firing stamps out (docs/generators.md).  Its own parts are checked in
              ;; the ordinary rule roles, so every arm below — `ist`, a head
              ;; existential, a negated antecedent — holds of the stamped rule exactly
              ;; as it holds of a written one, at whatever depth it sits.
              ;;
              ;; The recursion is the whole of the nesting rule: a stamped rule that
              ;; stamps a rule is read here exactly as the one above it was, and the
              ;; scoping rule composes to match — a variable belongs to the outermost
              ;; level whose antecedents mention it (`rules/nesting`), which is the
              ;; level whose firing grounds it.
              (contains? #{:sentence :consequent} role)
              (into (vec (mapcat #(walk :antecedent %) (rule-antecedents form)))
                    (walk :consequent (rule-consequent form)))
              :else
              [(str "a rule cannot stand as a " (clojure.core/name role) " literal")])
            (head-exists? form)
            (if (= :consequent role)
              (walk role (head-exists-body form))
              [(str "exists marks a rule consequent; it cannot stand in "
                    (clojure.core/name role) " position")])
            ;; A NAF body is a query standing in its literal's own position, so it is
            ;; checked in that role — an `(unknown (ist …))` is refused exactly as the
            ;; bare literal is, and for the sharper reason (`ist-read-problem`).  Only
            ;; where `unknown` means anything: it is an antecedent/exception construct,
            ;; and a top-level one is not a sentence this check is owed an opinion on.
            (and (unknown? form) (not= :sentence role)) (walk role (second form))
            (there-exists? form) (walk role (nth form 2))
            (aggregate? form)    (walk role (aggregate-body form))
            :else []))))]
    (walk :sentence sentence)))

(defn rename-vars
  "`form` with every variable `m` names replaced by the name it maps to — **one pass**,
  each position rewritten at most once.  Unmapped terms are left alone, and a vector
  stays a vector so a conjunction keeps its shape.

  One pass is the whole point, and it is what separates a **renaming** from a
  *substitution*.  `res/substitute` chases: it looks a variable up, then looks its
  value up, until it reaches something unbound — right for a unifier, whose bindings
  form an acyclic chain to a term (the occurs check is what guarantees that).  A
  renaming is a *permutation*, and permutations have cycles: applying `{?var0 ?var1,
  ?var1 ?var0}` to `(P ?var0 ?var1)` must give `(P ?var1 ?var0)`, where chasing would
  follow `?var0 → ?var1 → ?var0` and never stop.  So the two maps look alike and cannot
  share a function.

  This is the operation that carries a form between two canonical namings — the map
  `canonical-conjunction` hands back, a rule's `:varmap`, a cache's rename-back."
  [form m]
  (cond
    (and (variable? form) (contains? m form)) (get m form)
    (vector? form)     (mapv #(rename-vars % m) form)
    (sequential? form) (apply list (map #(rename-vars % m) form))
    :else form))

(defn originalize
  "Restore the author's variable names in `form` using a sentex's `:varmap`
  (`{?var0 ?x}`), for display.  `rename-vars` under the name the display path calls it."
  [form varmap]
  (rename-vars form varmap))

(defn canonical-conjunction
  "`[canonical varmap]` for a conjunction: every variable across **all** of `literals`
  renumbered `?var0 ?var1 …` by first occurrence under one shared numbering, and the map
  from each canonical name back to the name it replaced.

  One numbering across the whole conjunction, not one per literal — a variable shared
  between two literals is what joins them, and numbering them apart would break the join
  into two questions.

  The point of canonicalizing a *conjunction* (rather than a rule, which
  `canonicalize-rule` already does at storage) is identity: two conjunctions that differ
  only in what their variables are called become the same value, so a search that
  reaches one twice can recognize it.  `varmap` is how a solution found in canonical
  space is carried back to the names the caller used — applied with `rename-vars`, which
  is one pass because this map can be a permutation.

  `start` numbers from `?var<start>` instead of `?var0`, which is how a form is renamed
  **clear of** another one whose variables are already numbered `?var0 … ?var<start-1>`:
  the two namespaces become disjoint by construction rather than by inventing decorated
  names.  A stored rule is spelled `?var0 ?var1 …`, so unifying one against a conjunction
  spelled the same way needs exactly this before it can mean anything."
  ([literals] (canonical-conjunction literals 0))
  ([literals start]
   (let [[canon st] (number-forms (assoc empty-numbering :n (long start)) literals)]
     [canon (:vm st)])))

;; ---- α-renaming: canonical variable names for the index key -------------

(defn- alpha-rename
  "Rename variables to positional key names (?0, ?1, … by first occurrence) so forms
  differing only in variable names produce the same key.  A rule's stored sentence is
  already canonically numbered, so this is idempotent for rules; it still matters for
  a non-rule pattern (a query), whose variables keep the caller's names.  Preserves
  the dotted-rest marker `.` and every non-variable symbol; each anonymous `_` gets a
  fresh, unshared name.  Used only to build the index key — never the stored sentence
  or match bindings, so binding propagation is unaffected.

  A vector stays a vector, and renaming a *pair* of forms (a rule's sentence and its
  exception) numbers them jointly — the exception's variables are the sentence's, so
  renaming them apart would let two different exceptions key alike."
  [form]
  (let [n (atom 0)
        m (atom {})
        fresh (fn [] (let [v (symbol (str "?" @n))] (swap! n inc) v))]
    (letfn [(rn [x]
              (cond
                (and (symbol? x) (= "_" (clojure.core/name x))) (fresh)
                (variable? x) (or (@m x) (let [v (fresh)] (swap! m assoc x v) v))
                (vector? x) (mapv rn x)
                (sequential? x) (apply list (map rn x))
                :else x))]
      (rn form))))

;; ---- structural linearization -------------------------------------------
;; A nested compound argument is linearized into the trie path in **preorder**, so
;; each deep position is its own trie level: a pattern like
;; `(mass ?o (QuantityFn ?n Kilogram))` matches a stored `(QuantityFn 5 Kilogram)`
;; because `QuantityFn` and `Kilogram` are matchable and selective.  As one opaque
;; token a compound would match only by whole-value equality, and such a query would
;; miss.  See docs/indexing.md.
;;
;; The skip problem: once a compound spans several levels, a query variable that
;; binds a *whole* subterm — `(p ?y b)` where `?y = (F (G a))` — must advance past a
;; stored subterm of unknown length.  Each compound is preceded by an **arity marker**
;; carrying its element count, so `index/lookup` skips exactly that many top-level
;; children in O(1) (recursing for nested arity), with no balanced close-marker.
;;
;; The marker is a 2-vector `[::subterm k]`.  Nippy keeps keywords, ints, symbols and
;; strings as distinct types (see the storage note), and after linearization no trie
;; token is ever a vector — arguments are symbols/numbers/strings or (nested) lists,
;; and the connective frame is peeled — so a vector token is unambiguously a marker.
;; A `:false` / `:rule` key keeps its literals whole (a list token, never a vector),
;; and `lookup` treats such a list as a single opaque form, so those keys are
;; unchanged: only positive-fact keys linearize.

(def ^:private subterm-tag
  "The head of a structural arity marker — namespaced so it can never be a stored
  token (symbols, numbers, strings, and the `:false` / `:rule` / context slots are
  all type- or value-distinct from `[::subterm k]`)."
  ::subterm)

(defn subterm-mark  [k] [subterm-tag k])
(defn subterm-mark? [x] (and (vector? x) (= subterm-tag (nth x 0 nil))))
(defn subterm-arity [m] (nth m 1))

(defn- linearize
  "A term's preorder token stream: a compound `(F c…)` becomes an arity marker
  `[::subterm k]` (k = element count, functor included) followed by each element
  linearized; an atom is itself, one token."
  [form]
  (if (and (sequential? form) (seq form))
    (cons (subterm-mark (count form)) (mapcat linearize form))
    [form]))

(defn key-stream
  "The structural token stream for a fact body: the functor at the top level (no
  leading marker, so the `[pred …]` prefix and the `[:functor-root pred]` functor root stay
  the trie's first level), then each argument linearized.  Deterministic and
  compound-blind, so it composes with α-rename and dedup unchanged — an atom body
  degenerates to `[body]`."
  [body]
  (if (and (sequential? body) (seq body))
    (cons (first body) (mapcat linearize (rest body)))
    [body]))

;; ---- indexing key -------------------------------------------------------

(defn- key-tokens
  "The trie tokens for a sentex, with the `implies` / `and` rule frame canonicalized
  out and variables α-renamed.  A rule is keyed
  `[:rule <antecedents> <consequent> <assumption> <constraint>]` (a negative literal
  inside keeps its `not` — its polarity); a negative fact `[:false <body>]` (body kept
  whole so a `(not ?s)` pattern matches); a positive fact is its body **linearized** —
  the functor then each argument in preorder, so a nested compound is a run of trie
  levels rather than one opaque token (see the structural section above).

  `:assumption` (a choice rule) and `:constraint` (a contradiction rule) are **constant
  slots**, present (as nil) on every rule, so a choice / constraint rule and its bare
  twin get distinct keys and every rule keys at one depth — a ragged level would let a
  wildcard context slot descend into it and read child labels as handles.  An
  `exceptWhen` exception is *not* keyed here: it is
  a separate meta-sentex, so a rule and its excepted twin are the same sentex (asserting
  the exception amends the rule in place).

  Rules and `:false` bodies keep their literals whole (their tokens are lists, never
  markers): a rule pattern is only ever looked up for dedup, where whole-literal
  canonical numbering already gives an exact key, and a negative body stays one token
  so `(not ?s)` — whose body *is* a variable token — fans the child set the way it
  always has.  Linearizing them would add a dotted-rest (`(?pred . ?args)`) case and
  buy no retrieval selectivity, since neither is matched through a trie lookup of its
  own pattern.

  That last clause is a **constraint on the matcher, not an observation about it**.  A
  body kept whole means a negative key matches only *exactly*: `[:false (dog ?0) c]`
  and `[:false (dog Tom) c]` are different keys, and no part of the body is a level to
  narrow on, so a trie lookup of an open negative finds nothing rather than finding
  less.  `res/candidate-handles` is what honours it, routing an open negative to the
  secondary roots — which span both polarities — instead of here."
  [{:keys [sentence truth antecedent assumption constraint]}]
  (let [a (alpha-rename sentence)]
    (cond
      (some? antecedent) [:rule (vec (rule-antecedents a)) (rule-consequent a) assumption constraint]
      (= truth :false)   [:false (second a)]
      (sequential? a)    (vec (key-stream a))
      :else              [a])))

(defn path
  "The full trie path for a sentex: its (connective-free, α-renamed, structurally
  linearized) key tokens with the context appended as the final level."
  [sentex]
  (conj (key-tokens sentex) (:context sentex)))

(defn ground?
  "True when the sentence contains no pattern variables (anywhere, nested)."
  [{:keys [sentence]}]
  (not-any? variable? (tree-seq sequential? seq sentence)))

(defn subterms
  "Every subterm of a sentence — each atom and each compound subterm, recursively,
  the whole sentence included."
  [sentence]
  (if (sequential? sentence)
    (cons sentence (mapcat subterms sentence))
    (list sentence)))

(defn- literals
  "The atomic literals of a content form, stripping the structural connective *heads*
  `not` / `and` / `implies` (a `(not X)` unwraps to X; a conjunction/implication
  flattens to its parts) so they are never term-indexed — even when nested inside a
  rule.  A connective symbol in *argument* position (e.g. `(comment not \"…\")`,
  `(unaryPredicate not)`) is data, not a connective, and is left intact."
  [form]
  (if (and (sequential? form) (seq form))
    (case (first form)
      not           (literals (second form))
      (and implies) (mapcat literals (rest form))
      [form])
    [form]))

(defn content-forms
  "The connective-free literals a sentex is indexed and searchable by: a rule's
  antecedents and consequent, or a fact's positive body — each with its structural
  connective heads stripped, so `not` / `implies` / `and` never reach the term index.

  An exceptWhen exception is a *separate* meta-sentex, findable by the rule handle it
  names (its `(sentexHandle H)` is a ground compound the term index keeps); a rule's
  own content never mentions it.  The exception re-check index (`[:exception-index <predicate>]`)
  is what answers \"which rules watch this predicate\"."
  [sentex]
  (mapcat literals
          (if (some? (:antecedent sentex))
            (conj (vec (:antecedent sentex)) (:consequent sentex))
            [(body sentex)])))

(defn indexable-term?
  "A subterm worth an inverted-index entry: a non-variable symbol (predicate,
  individual, type, context) or a fully-ground compound.  Numbers, strings, and
  variables are dropped — useless lookup keys that only bloat the index."
  [t]
  (cond
    (number? t)     false
    (string? t)     false
    (variable? t)   false
    (symbol? t)     true
    (sequential? t) (not-any? variable? (tree-seq sequential? seq t))
    :else           false))

;; ---- which compounds earn a key: a floor and a ceiling ------------------
;; Both bound the same thing — which compounds are *stored* as keys — and neither touches
;; an atom: a symbol is keyed wherever it sits, at every depth, under every setting.  So
;; neither bound makes anything unfindable.  What a compound outside them costs is a read
;; rather than a key: `kb/find-sentexes` narrows on the atoms it contains and verifies the
;; candidates against their records (`probe-atoms` / `mentions?`, below).

(def ^:dynamic *min-indexed-depth*
  "How deep inside a content literal a ground **compound** must sit to earn its own
  inverted-index key — `0` being the literal itself, `1` a subterm of it, and so on.

  The default **1** drops each literal's own whole-compound key.  That key is what makes
  the token dictionary fact-scaled instead of vocabulary-scaled: a fact's body is a
  subterm of itself, so it mints one key holding exactly one handle, per record.  Over a
  12,070-record corpus of 511 names, 12,054 of the 12,565 distinct tokens are those keys;
  in the shipped starter, 1,108 of 1,383 — against 4 compounds that are genuinely nested.
  At the floor and deeper the nesting is what a probe is *for*: `(sentexHandle H)` inside
  an `exceptWhen` meta, the sentence inside an `(ist Ctx S)`.

  `2` and up also drop that wrapped sentence — the corpus where the nesting is itself
  per-record — at the cost of the read `ist` exists to serve, so the corpus decides.  `0`
  keys every compound, the literal included.

  It is read at **write** time, so moving it over a populated store changes what the next
  sentex is indexed under and leaves the keys already written where they are: a posting
  outside the new bound is stale rather than wrong (every read fetches the record, and a
  dead handle drops out there), and `reindex` is what applies a new setting wholesale.
  The token ids themselves are content-keyed and durable — a store keeps the ones it no
  longer mints, which is not a migration."
  1)

(def ^:const max-indexed-compound
  "Largest ground *compound* subterm (node count) the inverted term index gives its own
  key — the ceiling `*min-indexed-depth*` is the floor of.  Indexing a huge one stores a
  key holding the entire subtree (O(size) bytes, a full WAL frame on disk), so a deep
  ground term would cost O(depth²) index bytes and a wide one a key per level.  Above the
  bound the whole-compound key is dropped and every *symbol* it contains is still indexed
  individually (atoms are never capped), so the term stays findable — `find-sentexes`
  pays a read for it instead.  Scoped to `[:term-index]`: `indexable-term?` (which also
  drives the `[:argument-root]` argument roots) is untouched."
  64)

(defn- oversized-compound?
  "A ground compound too large to earn its own inverted-index key (see
  `max-indexed-compound`).  Early-cutoff: an oversized term is rejected after reading
  `max-indexed-compound`+2 nodes of the lazy `tree-seq`, so the check is O(cap), not
  O(size)."
  [t]
  (and (sequential? t)
       (< max-indexed-compound
          (count (take (+ 2 max-indexed-compound) (tree-seq sequential? seq t))))))

(defn- keyed-subterms
  "The subterms of one content literal that earn their own term-index key: every atom, at
  every depth, and each compound sitting at `floor` or deeper (`d` is `form`'s own depth,
  0 for the literal).  A compound shallower than the floor is still *descended into* — the
  floor drops its key, never its contents — so the atoms are the same set at every setting."
  [form ^long d ^long floor]
  (if (sequential? form)
    (let [inner (mapcat #(keyed-subterms % (inc d) floor) form)]
      (if (>= d floor) (cons form inner) inner))
    (list form)))

(defn index-terms
  "The distinct terms that make a sentex findable: the atoms of its connective-free
  content at every depth, plus each ground compound between `*min-indexed-depth*` and
  `max-indexed-compound`.  The sentex's context is added separately by the index."
  [sentex]
  (let [floor (long *min-indexed-depth*)]
    (into #{} (comp (mapcat #(keyed-subterms % 0 floor))
                    (filter indexable-term?)
                    (remove oversized-compound?))
          (content-forms sentex))))

(defn probe-atoms
  "The keys a **compound** probe narrows by: the indexable atoms it contains.  Every
  sentex holding the compound holds all of them — atoms are keyed at every depth under
  every bound — so their intersection is a superset of the answer, whatever key the
  compound itself does or does not earn.  A compound holding no indexable atom — no symbol
  anywhere in it — has nothing to narrow by and probes by its own key: at the default floor
  it can only occur nested, which is where it has one."
  [term]
  (let [as (into [] (comp (remove sequential?) (filter indexable-term?)) (subterms term))]
    (if (seq as) as [term])))

(defn mentions?
  "Does `sentex`'s connective-free content hold `term` as a subterm?  The question the
  term index answers wherever it has a key, asked of the record instead — the verify half
  of a compound probe, which turns `probe-atoms`' superset into the exact answer."
  [sentex term]
  (boolean (some (fn [form] (some #(= % term) (subterms form)))
                 (content-forms sentex))))

(defn ist
  "The reified `(ist <context> <sentence>)` term — like `ist` in the literature.
  It embeds a sentence (and its terms) inside another sentex; with the term index
  the wrapped sentence is findable from a sentence."
  [context sentence]
  (list ist-functor context (canon sentence)))
