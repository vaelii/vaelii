;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.sentex
  "The sentex — Vaelii's unit of knowledge: a sentence paired with the context it
  holds in (sentence + context = sentex).

  A *sentence* is a logical form written as a Clojure s-expression, e.g.
  (parentOf Tom Bob).  Ground (all constants) or a *pattern* with variables like ?x.
  A *context* names the situation / assumption frame it is asserted within.

  The structural connectives `not`, `implies`, and `and` are **canonicalized into
  the record** rather than left as data: a negation is at most one `(not S)` at the
  head of the sentence (double negation eliminated), read back by `negative?`, and a
  rule carries a decomposed `antecedent` (vector of patterns) and `consequent`.  So the
  connectives never reach the inverted **term index** (their heads are stripped, even
  nested inside a rule — see `content-forms`), and the positional **trie key** drops
  the `implies` / `and` rule frame; a negative literal keeps its `not` there, so a rule
  concluding `(flies ?x)` and one concluding `(not (flies ?x))` get distinct keys.

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

  A literal's `:sentence` holds its canonical, readable form for display and matching.  A
  rule holds no sentence: its `antecedent` and `consequent` are the one representation it
  keeps, and `sentence-of` builds the `implies` form from them.

  A sentex is one of two records — `LiteralSentex` (a literal: a signed predicate
  application — a fact or its negation, a metadata declaration, a query pattern) or
  `RuleSentex` (an implication) — so a literal sentex does not carry the rule-only slots
  (there are 100M+ of them), and each still round-trips through nippy with its type intact."
  (:refer-clojure :exclude [name])
  (:require [clojure.string :as str]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.types.sentex :as sentex-types])
  (:import [java.util.concurrent ConcurrentHashMap]))

(def ^:dynamic *symbol-pool-limit*
  "The most entries the pool holds across its two generations; each generation holds at
  most half.  The root starts at 1M, above the shipped ontology plus the whole of OpenCyc
  (~188k constants), and `size-symbol-pool` raises it when a store with a larger token
  dictionary opens.  Past the limit the generations rotate: a name mentioned since the
  previous rotation stays pooled, and a name not mentioned for two rotations leaves.
  Dynamic so a test exercises the rotation by binding a small limit, which an open does
  not move."
  1000000)

(defonce ^{:private true
           :doc "Interns the symbols sentences are built from, so the same predicate, individual,
  type, context, or variable name is a single shared object across every sentex that
  mentions it — the sharing a `parentOf` repeated through 100M+ facts buys, which
  dwarfs the pool's own footprint.  An atom over `[current previous]`, two
  `ConcurrentHashMap`s, because readers may intern beside the single writer.

  What bounds it is **not** the vocabulary.  A KB that only names things holds one entry
  per distinct name and is ontology-sized, but three writers mint a *fresh* symbol per
  fact: NAT reification (`nat/constant-for`, one content-named `nat/a…` per reified
  non-atomic term), head-existential skolemization (`skolem/skolemize-conclusion`, one witness per
  existential per firing frontier) and abduction (one scratch context each).  A disk store
  can also name more than the default limit outright: its token dictionaries intern every
  token they hold when the store opens, and a large store holds millions, so the open
  raises the limit first (`size-symbol-pool`).  Nothing hands an entry back on its own:
  the pool is static, process-wide and shared by every KB in it, so `retract!`, the store
  clears, `core/clear!`, a KB close and a catalog switch all leave it exactly as large as
  it was.

  So it holds two generations.  A lookup reads `current`, then `previous`, and a name found
  in `previous` is put into `current`.  When `current` reaches half of `*symbol-pool-limit*`
  it becomes `previous`, and the old `previous` is dropped.  A name read at least once per
  generation therefore keeps one shared object for as long as it is read, while the pool
  never holds more than the limit.  A rotation changes no answer, only a footprint:
  interning changes identity and never equality, so a dropped symbol stays alive in the
  records holding it, compares and hashes exactly as before, and is re-pooled on its next
  mention."}
  symbol-pool-generations
  (atom [(ConcurrentHashMap.) (ConcurrentHashMap.)]))

(defn- generation-limit
  "The entries `current` holds before it rotates: half of `*symbol-pool-limit*`, at least 1."
  ^long []
  (max 1 (quot (long *symbol-pool-limit*) 2)))

(defn size-symbol-pool
  "Raise the root of `*symbol-pool-limit*` to twice `tokens`, the entry count of a token
  dictionary a store is opening, and never lower it.  A caller calls it before the
  dictionary interns its tokens, so one generation holds them all.  A thread binding is
  left alone.  See docs/storage.md, \"Symbol interning\"."
  [tokens]
  (alter-var-root #'*symbol-pool-limit* max (* 2 (long tokens))))

(defn- rotate!
  "Make `gens`' `current` the `previous`, dropping the old `previous`, and answer the
  generations in force afterwards.  A lost compare-and-set means another thread rotated
  first, and its generations are answered instead of rotating a second time."
  [gens]
  (let [gens' [(ConcurrentHashMap.) (nth gens 0)]]
    (if (compare-and-set! symbol-pool-generations gens gens')
      gens'
      @symbol-pool-generations)))

(defn- pool-size
  "The entries in both generations.  A name moved out of `previous` is counted in both
  until `previous` is dropped, so this counts slots, which is what the footprint follows."
  ^long []
  (let [[^ConcurrentHashMap cur ^ConcurrentHashMap prev] @symbol-pool-generations]
    (+ (.size cur) (.size prev))))

(defn intern-sym
  "The pooled instance of symbol `s` (or `s` unchanged when it is not a symbol).
  Interning changes identity, never equality, so a pooled `?var0` still matches a
  fresh one as a binding key.

  A hit in `current` pays one `.get`.  A miss reads `previous`, rotates when `current` is
  full, and puts the symbol into `current`, as `previous`'s instance when `previous` held
  one.  A thread racing a rotation can put into the map that has just become `previous`;
  the entry stays findable there, so the race costs at most a missed sharing and never a
  wrong symbol."
  [s]
  (if (symbol? s)
    (let [gens @symbol-pool-generations]
      (or (.get ^ConcurrentHashMap (nth gens 0) s)
          (let [s    (or (.get ^ConcurrentHashMap (nth gens 1) s) s)
                gens (if (<= (generation-limit) (.size ^ConcurrentHashMap (nth gens 0)))
                       (rotate! gens)
                       gens)]
            (or (.putIfAbsent ^ConcurrentHashMap (nth gens 0) s s) s))))
    s))

;; No `:clear`, and the pool is the one cache here where that is a decision rather than
;; an omission: dropping it changes no answer (interning moves identity, never equality)
;; but throws away the sharing every symbol minted before it was paying for, and buys no
;; measurement in return — nothing counts a pool hit.  The rotation at the limit is a
;; footprint ceiling, not an instrument.
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
                 "or variable name, across every KB in this process, held in two "
                 "generations. At the limit the older generation is dropped, so a name "
                 "read since the last rotation stays pooled and a name unread for two "
                 "rotations leaves.")
  :read     (fn [_] {:entries (pool-size)})})

(defn canon
  "Canonicalize a sentence to a single sequential representation (PersistentList,
  recursively), interning every symbol through `symbol-pool-generations` on the way.  Substitution
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

(def variable?
  "A pattern variable: a symbol whose name starts with `?`, or `_`
  (`vaelii.impl.types.sentex/variable?`, which the columnar trie calls)."
  sentex-types/variable?)

(defn plain-symbol?
  "A symbol that is not a variable."
  [x]
  (and (symbol? x) (not (variable? x))))

(defn form-vars
  "Every variable anywhere in `form`, in order of occurrence and with duplicates, so a
  variable used twice counts twice (locality reads occurrence counts).  Lazy.  The one
  walk for a variable sequence: `rules`, `skolem`, `rewrite`, `asp.solve-context` and
  the exception closure check call it; `form-variables` is the set form."
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
  The collecting form of `some-symbol?`, and nil rather than `#{}` so a caller can branch
  on it without allocating for the common empty answer."
  [pred form]
  (letfn [(walk [acc x]
            (cond (sequential? x)              (reduce walk acc x)
                  (and (symbol? x) (pred x))   (conj (or acc #{}) x)
                  :else                        acc))]
    (walk nil form)))

;; The same two walks over *compounds* rather than symbols.  What asks for them is a
;; check about a shape a sentence may hold anywhere — a `do/` imperative, an `ist`
;; redirection, a quantifier, a non-finite measure — which has to descend arguments as
;; well as frames, and so touches every node of every sentence asserted to find a form
;; almost none of them contain.  Written directly for `some-symbol?`'s reason: the lazy
;; seq a `tree-seq` builds costs several times the predicate it carries, and the sentence
;; that holds nothing pays the whole of it.

(defn some-form
  "The first sub-form of `form` satisfying `pred` — `form` itself included, depth-first
  pre-order, the order `(first (filter pred (tree-seq …)))` yields — or nil.  Descends
  compounds and asks `pred` of every node, so `pred` decides what a node has to be.

  Nil is the whole of \"no match\", so a `pred` that holds of `nil` or `false` reads as
  one; every caller's holds of compounds, which are neither."
  [pred form]
  (if (pred form)
    form
    (when (sequential? form)
      (reduce (fn [_ x] (when-let [hit (some-form pred x)] (reduced hit))) nil form))))

(defn forms-where
  "Every sub-form satisfying `pred`, depth-first pre-order, as a vector.  The collecting
  form of `some-form` — a vector rather than nil, because its callers report *each* form
  they find rather than stopping at the first."
  [pred form]
  (letfn [(walk [acc x]
            (let [acc (if (pred x) (conj acc x) acc)]
              (if (sequential? x) (reduce walk acc x) acc)))]
    (walk [] form)))

;; ---- virtual rule wrappers (canonicalized into the record) ---------------
;; `(set/forwardRule (implies …))` is not data about a rule — it *is* how the rule's
;; direction is written.  Like not / implies / and, the wrapper canonicalizes into
;; the record (`:engines`, `:defeasible`, `:effect`) and never reaches the stored
;; sentence, so a rule carries its own direction rather than it living in a side index.
;; (`exceptWhen` is the exception: it is split off at the assert layer and stored as a
;; separate meta-sentex, not folded into the record — see `exceptWhen-meta`.)

(def rule-direction-wrappers
  '{set/forwardRule :forward, set/backwardRule :backward, set/inertRule :inert,
    set/forwardOnlyRule :forward-only, set/lazyForwardRule :lazy-forward})

(def default-rule-wrapper 'set/defaultRule)

(def assumption-rule-wrapper
  "`(set/assumptionRule (implies …))` — the rule's head is a *choice* offered to a
  solve, not a truth to derive.  Canonicalizes into `:effect :choose`; the rule never
  forward-chains into belief and is consulted only when grounding a solve
  (docs/solving.md)."
  'set/assumptionRule)

(def constraint-rule-wrappers
  "`(set/hardConstraint (implies …))` / `(set/softConstraint (implies …))` — the rule's
  head is a *contradiction marker* and its body a conjunctive nogood over background
  facts and choice-head patterns.  Canonicalizes into `:effect` (`:forbid` / `:penalize`);
  like an assumptionRule the rule never forward-chains, and a solve grounds its body
  (docs/solving.md).  A hard constraint renders as an ASPIF integrity constraint (models
  violating it are excluded); a soft one as a minimized violation."
  '{set/hardConstraint :hard, set/softConstraint :soft})

(def solve-rule-wrapper
  "`(set/solveRule (implies …))` — the rule also runs in a solve, as a normal rule
  (`h :- b`): a solve derives its head in every answer set whose atoms satisfy its body,
  and a constraint may name it.  Adds `:solve` to the record's `:engines`; a direction
  wrapper beside it says how the rule runs in base (backward when there is none), and
  `set/inertRule` makes it a rule that runs in a solve alone (docs/solving.md)."
  'set/solveRule)

;; ---- the record's two wrapper fields ------------------------------------
;; The wrappers state two things, and a rule record holds them as two fields
;; (`vaelii.impl.types.sentex`): `:engines`, which engines run the rule, and `:effect`,
;; what its head is.  Only a `:derive` rule has a choice of engines; a choice or
;; constraint head runs in a solve and nowhere else.

(def ^:private engine-sets
  "Every `:engines` value, each as one shared instance: a rule record holds one of these
  rather than a set of its own."
  (into {}
        (map (fn [s] [s s]))
        (for [f [nil :forward] b [nil :backward] l [nil :lazy] v [nil :solve]]
          (into #{} (remove nil?) [f b l v]))))

(defn canonical-engines
  "The shared instance of the engine set `engines`."
  [engines]
  (get engine-sets (set engines)))

(def direction-engines
  "The engines each `set/*Rule` direction runs a rule in, as the `:direction` opt and the
  wrappers spell them.  `:forward` and `:both` are one set: a forward rule answers
  backward goals too.  `:lazy` makes a backward rule's conclusion one a forward join
  proves on demand (docs/inference.md, \"A lazy-forward rule\")."
  {:backward     (canonical-engines #{:backward})
   :forward      (canonical-engines #{:forward :backward})
   :both         (canonical-engines #{:forward :backward})
   :forward-only (canonical-engines #{:forward})
   :lazy-forward (canonical-engines #{:backward :lazy})
   :inert        (canonical-engines #{})})

(def solve-engines
  "The engines of a choice or constraint rule: a solve alone reads it."
  (canonical-engines #{:solve}))

(defn engines-direction
  "The direction whose `set/*Rule` wrapper spells the base engines of `engines` (`:solve`
  aside) — `:backward`, `:forward`, `:forward-only`, `:lazy-forward` or `:inert`.  A
  forward rule stores its conclusions, so `:lazy` beside `:forward` spells `:forward`."
  [engines]
  (let [base (disj (set engines) :solve)
        fwd  (disj base :lazy)]
    (cond (= #{:forward :backward} fwd) :forward
          (= #{:forward} fwd)           :forward-only
          (= #{:backward :lazy} base)   :lazy-forward
          (= #{:backward} base)         :backward
          :else                         :inert)))

(defn wrapper-effect
  "The `:effect` a rule's head wrappers give it: `:choose` under `set/assumptionRule`,
  `:forbid` / `:penalize` under a hard / soft constraint, `:derive` under neither."
  [assumption constraint]
  (cond assumption            :choose
        (= :hard constraint)  :forbid
        (= :soft constraint)  :penalize
        :else                 :derive))

(defn effect-constraint
  "The constraint class of an `:effect` — `:hard` for `:forbid`, `:soft` for `:penalize`,
  nil otherwise."
  [effect]
  (case effect :forbid :hard :penalize :soft nil))

(defn rule-slots
  "The record's `[engines effect]` for a rule written with direction `dir` (nil when no
  direction wrapper was written) under the head wrappers `assumption` / `constraint`, and
  under `set/solveRule` when `solve?`.  An unwrapped rule runs backward, and an unwrapped
  generator forward, since no backward goal asks for a rule; `solve?` adds `:solve`.  A
  choice or constraint rule runs in a solve whatever `dir` says."
  ([dir assumption constraint generator?]
   (rule-slots dir assumption constraint false generator?))
  ([dir assumption constraint solve? generator?]
   (let [effect (wrapper-effect assumption constraint)]
     [(if (= :derive effect)
        (let [base (direction-engines (or dir (if generator? :forward :backward)))]
          (if solve? (canonical-engines (conj base :solve)) base))
        solve-engines)
      effect])))

(defn fielded-rule-slots
  "The `[engines effect]` of a rule frame that spells its wrappers as the three fields
  `direction` / `assumption` / `constraint` — the disk codec's rule tags 1, 3, 5, 7, 8 and
  9, a record thawed whole under those keys, and a dump frame keyed by them.  Such a frame
  always carries a direction."
  [direction assumption constraint]
  (rule-slots (or direction :backward) assumption constraint false))

(def except-wrapper
  "`(exceptWhen <query> <rule>)` — the rule does not conclude for a binding its
  exception holds of.  Unlike the other wrappers this one takes *two* arguments and
  captures one: the query.  The wrapper is split off at the assert layer and stored as
  a `(exceptWhen <query> (sentexHandle <rule-id>))` meta-sentex naming the rule, rather
  than folded into the rule record (see `exceptWhen-meta`)."
  'exceptWhen)

(def strength-wrapper
  "`(set/monotonic S)` — `S` asserted **known-true**.  In the `set/` namespace with the
  rule wrappers above and for their reason: it states how the sentence is *asserted*
  rather than anything the sentence says, and never reaches the store as a functor.

  Read in two positions.  Around a **whole sentence** it is `{:strength :monotonic}`,
  read by the text KB format and by `assert`, `check` and `try-assert` alike
  (`peel-strength`).  Around an `exceptWhen`'s *query* it states the **exception's** own
  class, the one thing an `opts` cannot say, since one `opts` reaches both halves of an
  `exceptWhen` (`peel-exception-strength`).  Anywhere else, on the wrapper chain or
  inside the sentence, it is refused (`:shape`)."
  'set/monotonic)

(def inert-wrapper
  "`(set/inert S)` — `S` stored through `assert-inert`: indexed and durable, never a
  premise.  Read by the text KB format alone, around a whole form; `assert`, `check` and
  `assert-inert` refuse it on the wrapper chain and inside the sentence (`:shape`), since
  it names another entry point rather than an option of theirs."
  'set/inert)

(defn form-peel
  "`[sentence opts problem]` for one whole form: `(set/monotonic S)` is `S` with
  `{:strength :monotonic}`, `(set/inert S)` is `S` with `{:inert true}`, and anything
  else is itself with nil.  `problem` is the `:shape` refusal of a wrapper around no
  sentence or two, or around the other wrapper, since an inert sentex has no strength."
  [form]
  (let [wrapper? #(and (sequential? %) (#{strength-wrapper inert-wrapper} (first %)))]
    (if (wrapper? form)
      (let [w (first form)]
        (cond
          (not= 2 (count form))
          [form nil {:type :shape :form form
                     :message (str "(" w " …) wraps exactly one sentence, got "
                                   (dec (count form)) ": " (pr-str form))}]

          (wrapper? (second form))
          [form nil {:type :shape :form form
                     :message (str "(" w " …) wraps a sentence, not another (" (first (second form))
                                   " …): an inert sentex has no strength, and a strength is"
                                   " stated once: " (pr-str form))}]

          :else [(second form) (if (= w inert-wrapper) {:inert true} {:strength :monotonic}) nil]))
      [form nil nil])))

(defn strength-peel
  "`[sentence opts problem]`: `sentence` with a whole-form `(set/monotonic S)` read as `S`
  and `:strength :monotonic` in `opts`, or both as they came with the `:shape` problem
  that refuses them, or nil.  A `(set/inert S)` comes back as it came, for the wrapper
  chain to refuse."
  [sentence opts]
  (if (and (sequential? sentence) (= strength-wrapper (first sentence)))
    (let [[s _ problem] (form-peel sentence)
          given        (:strength opts)]
      (cond
        problem [sentence opts problem]

        (and (some? given) (not= :monotonic given))
        [sentence opts {:type :shape :sentence sentence :strength given
                        :message (str "(" strength-wrapper " …) states :monotonic and opts"
                                      " state :strength " given ": " (pr-str sentence))}]

        :else [s (assoc opts :strength :monotonic) nil]))
    [sentence opts nil]))

(defn peel-strength
  "`[sentence opts]`: a whole-form `(set/monotonic S)` read as `S` asserted
  `{:strength :monotonic}`, as the text KB format reads it, and anything else as it came.
  Throws `:shape` for a malformed wrapper and for one beside an `opts` `:strength` other
  than `:monotonic`."
  [sentence opts]
  (let [[s o problem] (strength-peel sentence opts)]
    (when problem
      (throw (ex-info (:message problem) (dissoc problem :message))))
    [s o]))

(defn- strength-wrapped
  "`[wrapped]` when `form` is a `(set/monotonic X)`, `::malformed` when it is one written
  with the wrong number of arguments, nil when it is not one at all.

  Three answers rather than two, because the middle one has to be refused rather than
  passed through: a bare `(set/monotonic)` handed on would reach the naming checks as a
  literal whose functor is a namespace-qualified symbol, and be refused there for the
  wrong reason.  A vector, so a legitimately falsy wrapped form is still a hit."
  [form]
  (when (and (sequential? form) (seq form) (= strength-wrapper (first form)))
    (if (= 2 (count form)) [(second form)] ::malformed)))

(defn- misplaced-wrapper-problem
  "The `:shape` problem a `(set/monotonic …)` or `(set/inert …)` is refused with where
  `assert` does not read it, or nil when `form` is neither."
  [form]
  (when (and (sequential? form) (seq form))
    (condp = (first form)
      strength-wrapper
      {:type :shape :sentence form
       :message (str "(" strength-wrapper " …) states an assertion's strength, read around"
                     " a whole sentence or an exceptWhen query and nowhere else: "
                     (pr-str form))}
      inert-wrapper
      {:type :shape :sentence form
       :message (str "(" inert-wrapper " …) stores a sentence inert, which is assert-inert's"
                     " entry point; only the text KB loader reads the wrapper: "
                     (pr-str form))}
      nil)))

(defn- nested-wrapper-problem
  "`misplaced-wrapper-problem` of the first form at any depth of `form`, `form` included,
  that is a `(set/monotonic …)` or a `(set/inert …)`, or nil.  An `(ist Ctx S)` answers
  nil: every entry point reads S as a whole sentence of its own, and walks it then."
  [form]
  ;; 'ist is `ist-functor`, defined with the connectives below
  (when-not (and (sequential? form) (= 'ist (first form)))
    (some-> (some-form misplaced-wrapper-problem form) misplaced-wrapper-problem)))

(defn- walk-exception-strength
  "`[form monotonic? problem]` — `form` with a `(set/monotonic …)` taken off every
  `exceptWhen` query on its wrapper chain, whether one was there, and the `:shape`
  problem the chain is refused with: a malformed query wrapper, or a
  `nested-wrapper-problem` anywhere else on the chain or inside the sentence it ends at.

  One walk answering three questions, because `check` wants the problem and `assert`
  wants the peeled form, and a second traversal is a second reading of the chain to keep
  in step.  Two `exceptWhen`s written together conjoin into **one** meta-sentex, so a
  wrapper on either query says the whole exception is known-true."
  [form]
  (if (and (sequential? form) (seq form))
    (let [h (first form)]
      (cond
        (and (= h except-wrapper) (= 3 (count form)))
        (let [q     (second form)
              w     (strength-wrapped q)
              bad?  (= ::malformed w)
              mono? (vector? w)
              q'    (if mono? (first w) q)
              [inner inner-mono? inner-problem] (walk-exception-strength (nth form 2))]
          [(list except-wrapper q' inner)
           (or mono? inner-mono?)
           (or (when bad?
                 {:type :shape :sentence form
                  :message (str "(" strength-wrapper " …) on an exceptWhen query wraps"
                                " exactly one query, got " (dec (count q)) ": "
                                (pr-str q))})
               (nested-wrapper-problem q')
               inner-problem)])

        (or (= h default-rule-wrapper)
            (= h assumption-rule-wrapper)
            (= h solve-rule-wrapper)
            (contains? constraint-rule-wrappers h)
            (contains? rule-direction-wrappers h))
        (let [[inner mono? problem] (walk-exception-strength (second form))]
          [(list h inner) mono? problem])

        :else [form false (nested-wrapper-problem form)]))
    [form false nil]))

(defn exception-strength-problem
  "The `:shape` problem a malformed strength wrapper on an `exceptWhen` query, or a
  `(set/monotonic …)` / `(set/inert …)` elsewhere on the wrapper chain or inside the
  sentence, is refused with, or nil.  A value for `check`, and the `ex-info`
  `peel-exception-strength` throws — so the two entry points refuse the same input in the same words, differing only in the
  delivery."
  [form]
  (nth (walk-exception-strength form) 2))

(defn peel-exception-strength
  "`[sentence monotonic?]`: `sentence` with the strength wrapper taken off its `exceptWhen`
  query, and the class that wrapper stated for the exception alone.  `assert` passes one
  `opts` to both halves of an `(exceptWhen Q R)`, which cannot state a known-true exception on
  a default rule.  Nothing below the assert entry point sees the wrapper.  A sentence with no
  wrapper is returned as the same object."
  [sentence]
  (let [[peeled mono? problem] (walk-exception-strength sentence)]
    (when problem
      (throw (ex-info (:message problem) (dissoc problem :message))))
    (if mono? [peeled true] [sentence false])))

(defn- wrapper-stack
  "The `set/*` wrapper heads around one rule, outermost first, read through any
  `exceptWhen` and past a constraint wrapper's leading priority.  Stops at the first form
  that is not a wrapper, so a generator's generated rule is a stack of its own."
  [form]
  (loop [f form, acc []]
    (let [h (when (and (sequential? f) (seq f)) (first f))]
      (cond
        (or (= h default-rule-wrapper) (= h assumption-rule-wrapper) (= h solve-rule-wrapper)
            (contains? rule-direction-wrappers h))
        (recur (second f) (conj acc h))
        (constraint-rule-wrappers h)
        (recur (if (and (= 3 (count f)) (integer? (second f))) (nth f 2) (second f)) (conj acc h))
        (and (= h except-wrapper) (= 3 (count f))) (recur (nth f 2) acc)
        :else acc))))

(defn solve-wrapped?
  "Is `form` a rule written under `set/solveRule`, at any depth of its wrapper stack?"
  [form]
  (boolean (some #{solve-rule-wrapper} (wrapper-stack form))))

(defn wrapper-stack-problems
  "What is wrong with the combination of `set/*` wrappers around one rule, as strings.  A
  direction wrapper or `set/defaultRule` states how a rule runs; `set/assumptionRule` (a
  choice), `set/hardConstraint` and `set/softConstraint` state its head.  Four combinations
  state nothing the record can hold:

  - two different direction wrappers;
  - two different head wrappers;
  - a head wrapper with a direction wrapper, `set/defaultRule` or `set/solveRule`, since a
    choice or constraint head is decided by a solve and never chained or believed
    (docs/solving.md);
  - `set/solveRule` with `set/defaultRule`, since one answer set has no defeat to apply."
  [form]
  (let [stack (wrapper-stack form)
        ;; a wrapper repeated says one thing twice, so only distinct ones count
        dirs  (into [] (comp (filter #(contains? rule-direction-wrappers %)) (distinct)) stack)
        heads (into [] (comp (filter #(or (= assumption-rule-wrapper %) (constraint-rule-wrappers %)))
                             (distinct))
                    stack)
        modes (filterv #(or (contains? rule-direction-wrappers %) (= default-rule-wrapper %)
                            (= solve-rule-wrapper %))
                       stack)]
    (cond-> []
      (< 1 (count dirs))
      (conj (str "a rule takes one direction wrapper, got " (str/join " and " dirs)))
      (< 1 (count heads))
      (conj (str "a rule's head is one of a choice (set/assumptionRule), a hard constraint"
                 " and a soft one, got " (str/join " and " heads)))
      (and (seq heads) (seq modes))
      (conj (str (first heads) " is decided by a solve and never chained, so it takes no "
                 (str/join " or " (distinct modes)) " — drop the wrapper"))
      (and (some #{solve-rule-wrapper} stack) (some #{default-rule-wrapper} stack))
      (conj (str "set/solveRule takes no set/defaultRule: one answer set has no defeat to"
                 " apply, so a defeasible rule has no reading inside a solve")))))

;; ---- structural connectives (canonicalized into the record) -------------

(def not-functor  'not)
(def rule-functor 'implies)
(def and-functor  'and)
(def or-functor   'or)
(def ist-functor  'ist)

(def no-match
  "The reserved constant a read-mode reify resolves a never-minted NAT to, and a goal's
  application with no correspondence is replaced by.  No stored sentex names it, and it
  denotes no term, so only the stored-fact prover reads a literal holding it at a term
  position (`res/names-no-match?`)."
  'nat/no-match)

(def root-context
  "The context the upper ontology is stored in, every `genlCx` edge with it, and the one
  every context the shipped topology wires in sees (docs/contexts.md)."
  'CxUniverse)
(def dot-marker   '.)

(defn rest-marker?
  "Does `xs`, a list or a suffix of one, open a dotted rest: the dot marker, then one
  variable, then nothing?  A `.` in any other place is refused (`dot-problem`)."
  [xs]
  (and (sequential? xs) (= dot-marker (first xs)) (variable? (second xs)) (nil? (nnext xs))))

(defn dotted?
  "Is `form` a dotted rest pattern, `(?pred . ?args)` or `(rel A . ?rest)`: a list that
  ends in the dot marker and one variable?"
  [form]
  (and (sequential? form)
       (loop [s (seq form)]
         (cond (nil? s)                  false
               (not= dot-marker (first s)) (recur (next s))
               (rest-marker? s)          true
               :else                     (recur (next s))))))

(defn positional
  "The elements of `form` before its rest marker, or all of them when it is not dotted."
  [form]
  (if (dotted? form) (drop-last 2 form) form))

(defn misplaced-dot
  "The first list in `form`, depth-first, that holds a `.` other than its rest marker,
  or nil when every `.` in it opens a rest (`rest-marker?`)."
  [form]
  (when (sequential? form)
    (loop [s (seq form)]
      (cond (nil? s)                    (some misplaced-dot form)
            (not= dot-marker (first s)) (recur (next s))
            (rest-marker? s)            (some misplaced-dot form)
            :else                       form))))

(defn dot-problem
  "The `:shape` problem a sentence or goal holding a misplaced `.` is refused with, under
  key `k` (`:sentence` or `:goal`), or nil.  `.` is the rest marker's syntax and names no
  term, so the write, import and read entry points refuse it whatever `:naming` says."
  [k form]
  (when-let [m (misplaced-dot form)]
    {:type :shape k form :misplaced-dot m
     :message (str "'.' in " (pr-str m) " is not a rest marker: a '.' is legal only"
                   " before a list's last element, and only when that element is a"
                   " variable, as in (?pred . ?args)")}))

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

(def defeat-functor
  "`(defeat <handle>)` — a meta-sentex the engine derives that removes the sentex the handle
  names from belief at the context it is stored in and every context that sees it, read at
  read time.  `assert` refuses it in every literal (`checks/check-no-defeat`)."
  'defeat)

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

(defn names-a-handle?
  "Does `sentence` name a stored sentex by handle?  A `(sentexHandle N)` term anywhere
  inside is a handle by shape.  An `(except N)` carries a bare integer, a handle by
  position, indistinguishable from the `86400` in `(conversionFactor Day Second 86400)`;
  so it is recognised by its functor instead."
  [sentence]
  (boolean (or (and (sequential? sentence) (= except-functor (first sentence)))
               (some sentex-handle? (tree-seq sequential? seq sentence)))))

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

(defn negation?
  "Is `form` a negation `(not <body>)`?  Arity checked, so a `not` at any other arity
  is not one."
  [form]
  (and (sequential? form) (= not-functor (first form)) (= 2 (count form))))

(def exact-arity-classes
  "What each exact-arity class membership says the arity is.  The `arity` sentexes and these
  memberships derive each other through the core.txt rules, but a `{:chain? false}` assert or
  a KB loaded without the rules has only what was written, so both spellings are read.

  core.txt ships fifteen classes: `unary` … `quinary` are relation-wide and ten specialize
  them by kind, so a function's arity may be written `(binary_function F)`.  The arity readers
  read a stored membership by its own functor (`arity-binding`).  The spellings of one term
  never disagree: a class and its specializations map to one number.  The table lives here,
  below the index, because `arity/relation-length` and `kb/relation?` read it."
  '{unary 1 binary 2 ternary 3 quaternary 4 quinary 5
    unary_predicate 1 binary_predicate 2 ternary_predicate 3
    quaternary_predicate 4 quinary_predicate 5
    unary_function 1 binary_function 2 ternary_function 3
    quaternary_function 4 quinary_function 5})

(def arg-projections
  "Each binary projection of `arg`, with the position it projects: `(argN P T)` states
  what `(arg P N T)` states.  The declaration checks and the integrity census read it."
  '{arg1 1 arg2 2 arg3 3 arg4 4 arg5 5})

(def variable-arity-classes
  "The memberships that release a relation from one exact length."
  '#{variable_arity variable_arity_predicate variable_arity_function})

(defn fact-shape
  "`[f n]` for a record `sx` holding a positive fact of `n` arguments with a plain symbol
  functor, else nil.  A sentence about to be written is asked as `{:sentence s}`."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (<= 2 (count s)))
      (let [f (first s)]
        (when (and (plain-symbol? f) (not= not-functor f))
          [f (dec (count s))])))))

(def arity-binding-functors
  "The functors of the facts `arity-binding` answers a length binding for."
  (into '#{arity arityMin} cat [(keys exact-arity-classes) variable-arity-classes]))

(defn arity-binding
  "`[P kind value]` for the sentence `s` of a stored fact that binds a relation's length,
  else nil: `(arity P n)` and an exact-arity class membership bind `:exact n`, a
  `variable_arity` membership `:var nil`, and `(arityMin P m)` `:min m`.  The index posts
  each under its binding family (`vaelii.impl.kv`), which `arity/relation-length` reads."
  [s]
  (when (seq? s)
    (let [[f p v] s
          n       (count s)]
      (when (and (symbol? f) (symbol? p) (not (variable? p)))
        (cond
          (and (= 3 n) (= 'arity f) (integer? v) (pos? v))    [p :exact v]
          (and (= 3 n) (= 'arityMin f) (integer? v) (pos? v)) [p :min v]
          (and (= 2 n) (exact-arity-classes f))               [p :exact (exact-arity-classes f)]
          (and (= 2 n) (variable-arity-classes f))            [p :var nil])))))

(defn fact-arity-binding
  "`arity-binding` of the sentence of a record `sx` holding a fact, else nil."
  [sx]
  (when (nil? (:antecedent sx))
    (arity-binding (:sentence sx))))

(defn implies?
  "Is `form` a rule form `(implies <ante> <conseq>)`?  Arity checked: an `implies` at
  any other arity is never read as a rule — `rule-consequent` is an `nth`, so an
  arity-4 form read as a rule would silently drop its tail.  `connective-problems`
  refuses the malformed form at both entry points before this question is asked."
  [form]
  (and (sequential? form) (= rule-functor (first form)) (= 3 (count form))))

(defn- peel-not
  "Strip leading `not` wrappers, returning [polarity body] with double negation
  eliminated: an even number of nots ⇒ :positive, an odd number ⇒ :negative."
  [form]
  (loop [f form, positive true]
    (if (negation? f)
      (recur (second f) (not positive))
      [(if positive :positive :negative) f])))

(defn negative?
  "Is `sx` a negative literal — a sentex whose sentence is `(not S)`?  The record keeps
  no separate sign: construction leaves at most one `not`, at the head (`peel-not`), so
  the head is the whole answer.  False for a rule, which holds no sentence."
  [sx]
  (negation? (:sentence sx)))

(defn positive-fact?
  "Is `sx` a stored literal that is not negative: not nil, no rule, no `(not S)`?"
  [sx]
  (and sx (nil? (:antecedent sx)) (not (negative? sx))))

(defn polarity
  "`:negative` for a negative literal, `:positive` for any other sentex — the keyword a
  reader compares or hashes where it wants one value for the sign."
  [sx]
  (if (negative? sx) :negative :positive))

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

;; ---- disjunction: the connective that never reaches the record ----------
;; `or` is the one structural connective with **no** slot of its own.  A rule whose
;; antecedent disjoins is polycanonicalized into one rule per alternative
;; (`rules/expand-antecedent`), exactly as a conjunctive consequent is split into one
;; rule per conjunct — so by the time anything is canonicalized, indexed or stored, the
;; `or` is gone and each alternative is an ordinary rule.  Nothing downstream of the
;; assert entry point has to know the connective exists.  See docs/canonicalization.md.

(defn disjunction?
  "Is `form` a disjunction `(or <alternative> ...)`?  Arity is *not* checked here — an
  empty `(or)` is a disjunction that no alternative satisfies, and naming it as one is
  what lets `rules/disjunction-problems` refuse it by that name."
  [form]
  (and (sequential? form) (seq form) (= or-functor (first form))))

(defn disjuncts
  "The alternatives a disjunction offers."
  [form]
  (vec (rest form)))

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

(defn sentence-of
  "A sentex's canonical sentence: a literal's `:sentence`, or for a rule the
  `(implies <antecedent> <consequent>)` form `rule-sentence` builds from its two fields.
  A rule record holds only the fields, so this is the one place its whole form comes
  from — the form `path` keys on and `core/readable-sentence` renames for display.
  Keyword reads only, so a sentex map off the wire answers the same as the record."
  [sx]
  (if (some? (:antecedent sx))
    (rule-sentence (:antecedent sx) (:consequent sx))
    (:sentence sx)))

;; ---- aggregation: counting what the KB believes --------------------------
;; These sit above the canonicalization because `deferred-predicates` is built from them.
;; See docs/aggregate.md.

(def aggregate-functors
  "The five aggregation operators, mapped to the reduction each names.  All five take
  the shape `(<op> ?n ?v <body>)`."
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

(def structure-constructors
  "The data-structure constructors and the kind of structure each builds."
  '{ListFn :list MultisetFn :multiset SetFn :set MapFn :map})

(def structure-relations
  "The relations over a structure term, the structure last and the outputs first:
  `(elementOf ?x ?s)`, `(cardinalityOf ?n ?s)`, `(multiplicityOf ?n ?x ?s)` and
  `(valueAt ?v ?k ?s)`, with the number of leading outputs each.  `provers/StructureProver`
  computes them and the corresponding predicates, so both are deferred."
  '{elementOf 1 cardinalityOf 1 multiplicityOf 2 valueAt 2})

(def structure-predicates
  "Each constructor's corresponding predicate, the structure first: `(setOf ?set .
  ?elements)` holds when `?set` is `(SetFn . ?elements)`, and `(entryOf ?entry ?key
  ?value)` when `?entry` is `(EntryFn ?key ?value)`."
  '{listOf ListFn multisetOf MultisetFn setOf SetFn mapOf MapFn entryOf EntryFn})

(def structure-functions
  "The functions whose open application a rule or a goal reads through its corresponding
  predicate rather than matches as written (docs/nat.md, \"A data structure is a
  structural term\")."
  (set (vals structure-predicates)))

(def deferred-predicates
  "Predicates that *consume* bindings rather than produce them: evaluable tests and
  computations.  Antecedent order is operational for these, so canonical ordering keeps them
  last, in the author's relative order.

  - `different` is a ground-only test over the equality closure (`vaelii.impl.provers`) and
    is never stored.  It is absent from `comparison-siblings` and `chained-comparisons`
    because it is not transitive: `A≠B` and `B≠C` say nothing about `A` and `C`
    (docs/equality.md).
  - `unknown` consumes the bindings its argument's `free-vars` need.  `thereExists` is absent:
    a standalone one is desugared to its body (`desugar-there-exists`, docs/naf.md).
  - The quantity comparisons (`sameQuantity`, `quantityLessThan`, `quantityGreaterThan`,
    `quantityLessThanOrEqual`, `quantityGreaterThanOrEqual`) are computed by `QuantityProver`
    from two ground measures.  They fold onto no arithmetic sibling: `sameQuantity` is
    symmetric, and a measure chain crosses units.
  - The aggregates need their group variable bound first (docs/aggregate.md).
  - `matchesPattern` and the value kinds (`integer`, `string`, `number`, `boolean`,
    `keyword`, `character`) are computed by `EvaluableProver` from ground arguments.  A value
    kind of a constant or a compound is read from the store (`provers/term-value-kind-goal?`)."
  (-> '#{evaluate lessThan greaterThan different unknown matchesPattern
         integer string number boolean keyword character
         sameQuantity quantityLessThan quantityGreaterThan
         quantityLessThanOrEqual quantityGreaterThanOrEqual}
      (into (keys aggregate-functors))
      (into (keys structure-relations))
      (into (keys structure-predicates))))

(defn deferred-literal?
  "Is this literal one of the deferred (evaluable) ones?  Public because the storage
  canonicalization here and the query planner (`vaelii.impl.plan`) must hold back
  exactly the same set — if the two ever disagreed, a planner could hoist an
  `evaluate` above the literal binding its arguments, which yields no solutions
  rather than an error."
  [l]
  (and (sequential? l) (seq l) (contains? deferred-predicates (first l))))

;; ---- negation as failure: `unknown`, `thereExists` and `forall` -----------
;; See docs/naf.md.

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

(defn conjunction?
  "Is `form` an `(and …)` conjunction?"
  [form]
  (and (sequential? form) (= and-functor (first form))))

(defn conjuncts
  "`form`'s conjunct literals: an `(and …)` flattened all the way down, anything else as
  a one-element vector.  An `(and)` yields none (docs/naf.md, \"`S` may be a
  conjunction\")."
  [form]
  (letfn [(flat [q] (if (conjunction? q) (mapcat flat (rest q)) [q]))]
    (vec (flat form))))

(defn naf-query-conjuncts
  "The conjunct literals an `(unknown S)` antecedent's query is evaluated as:
  `conjuncts` of `S`.  The `unknown` spelling of `exception-query-conjuncts`."
  [unk]
  (conjuncts (second unk)))

(def forall-functor 'forall)

(defn forall?
  "Is `form` a `(forall <var-or-vars> (implies Body Head))` universal?"
  [form]
  (and (sequential? form) (= forall-functor (first form)) (= 3 (count form))))

(defn quantified-vars
  "The variables a `thereExists` or `forall` binder introduces, as a set: its second
  element is a variable or a sequence of them.  A written vector becomes a list under
  `canon`, so this keys on `sequential?`, not `vector?`.  Non-variables are dropped;
  `check-naf-closed` refuses a rule whose binder holds one."
  [form]
  (let [q (second form)]
    (cond
      (variable? q)   #{q}
      (sequential? q) (into #{} (filter variable?) q)
      :else           #{})))

;; ---- head existential: an existential variable in a rule consequent -------
;; `(exists <var-or-vars> C)` marks a consequent variable no antecedent binds, which
;; forward firing skolemizes (docs/skolem.md).

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

(defn- check-binder
  "Throw `:not-well-formed` unless the `thereExists`, `forall` or head `exists` `q` binds
  a variable or a sequence of variables.  A constant in the binder binds nothing, so the
  body reads it as that constant: `(unknown (thereExists Kid (owns ?x Kid)))` holds of
  every `?x` that owns no individual named `Kid`."
  [q]
  (let [b (second q)]
    (when-not (or (variable? b) (and (sequential? b) (every? variable? b)))
      (throw (ex-info (str (first q) " binds " (pr-str b) ", which is not a variable or a"
                           " list of variables — a constant in the binder binds nothing,"
                           " so the body reads it as that constant: write a variable")
                      {:type :not-well-formed :quantifier q})))))

(defn free-vars
  "The variables of `form` that must be bound before it can be evaluated: every variable
  it mentions, minus those a quantifier inside it binds.  `unknown` is transparent,
  `thereExists` and `forall` subtract their binder, and an aggregate subtracts its `?v`
  and its `?n` (docs/naf.md, \"Fully bound to evaluate\")."
  [form]
  (cond
    (variable? form)     #{form}
    (not (sequential? form)) #{}
    (unknown? form)      (free-vars (second form))
    (or (there-exists? form) (forall? form))
    (into #{} (remove (quantified-vars form)) (free-vars (nth form 2)))
    (aggregate? form)    (disj (into #{} (free-vars (aggregate-body form)))
                               (aggregate-value-var form)
                               (when (variable? (second form)) (second form)))
    :else                (into #{} (mapcat free-vars) form)))

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
  reads all of them.  A structure relation writes its leading outputs, and a corresponding
  predicate writes the structure it builds from the elements."
  (-> '{evaluate 1}
      (into (map (fn [f] [f 1])) (keys aggregate-functors))
      (into structure-relations)
      (into (map (fn [f] [f 1])) (keys structure-predicates))))

(defn- reads-structure?
  "Does corresponding-predicate literal `g` run the other way under the variables `bound`:
  its structure's variables all bound and its elements' not, so it reads the elements?"
  [g bound]
  (and (contains? structure-predicates (first g))
       (every? bound (form-vars (second g)))
       (not (every? bound (mapcat form-vars (nnext g))))))

(defn deferred-output-vars
  "The variables a deferred literal **binds** — `evaluate`'s first argument, an
  aggregate's `?n`, and nothing at all for a pure test like `lessThan` or `different`.
  Under `bound`, a corresponding predicate whose structure is bound binds its elements."
  ([g] (deferred-output-vars g #{}))
  ([g bound]
   (cond
     (not (sequential? g))      #{}
     (reads-structure? g bound) (into #{} (mapcat form-vars) (nnext g))
     :else (into #{} (mapcat form-vars) (take (get deferred-output-arity (first g) 0) (rest g))))))

(defn deferred-input-vars
  "The variables a deferred literal must have bound before it can run: `free-vars` for
  `unknown` and the aggregates, and every argument it does not write for the rest.  Under
  `bound`, a corresponding predicate whose structure is bound reads only the structure."
  ([g] (deferred-input-vars g #{}))
  ([g bound]
   (cond
     (not (sequential? g))            #{}
     (or (unknown? g) (aggregate? g)) (free-vars g)
     (reads-structure? g bound)       (set (form-vars (second g)))
     :else (into #{} (mapcat form-vars) (drop (get deferred-output-arity (first g) 0) (rest g))))))

(defn census-bound-vars
  "The variables an aggregate's census `body` binds **for itself**: what its generator
  conjuncts match, plus what its computed conjuncts write.  An inner `thereExists` binder
  is not among them.  Read by `check-naf-closed`'s census check and by
  `provers/AggregateProver`'s applicability (docs/aggregate.md, \"Grouping\")."
  [body]
  (let [cs       (conjuncts body)
        computed (fn [c] (or (unknown? c) (deferred-literal? c)))]
    (into (into #{} (mapcat free-vars) (remove computed cs))
          (mapcat deferred-output-vars)
          (filter computed cs))))

(defn there-exists-antecedent?
  "Is antecedent `form` a standalone positive `thereExists`?  On an antecedent list a
  `thereExists` under `unknown` is never an element."
  [form]
  (there-exists? form))

(defn desugar-there-exists
  "Rule antecedents `antes` with each standalone positive `(thereExists ?x S)` replaced
  by the `conjuncts` of `S`, spliced in (docs/naf.md, \"Standalone positive
  `thereExists` desugars\")."
  [antes]
  (into [] (mapcat (fn [a] (if (there-exists-antecedent? a) (conjuncts (nth a 2)) [a]))) antes))

(defn- unproducible-inputs
  "The quantified variables of NAF query `q` that a computed conjunct reads and no
  generator conjunct of the same query produces, recursing into each nested `unknown`.
  The variables the quantifier does not bind are the outer closure check's (docs/naf.md,
  \"The conjunction is joined\")."
  [q]
  (let [body     (if (there-exists? q) (nth q 2) q)
        cs       (conjuncts body)
        qs       (if (there-exists? q) (quantified-vars q) #{})
        computed (fn [c] (or (unknown? c) (deferred-literal? c)))
        gen-vars (into #{} (mapcat form-vars) (remove computed cs))]
    (concat (mapcat (fn [c] (filter #(and (qs %) (not (gen-vars %))) (deferred-input-vars c)))
                    (filter computed cs))
            (mapcat #(unproducible-inputs (second %)) (filter unknown? cs)))))

(defn desugar-forall-literal
  "The nested NAF an antecedent `(forall ?y (implies Body Head))` is:

      (unknown (thereExists ?y (and Body… (unknown Head))))

  A conjunctive `Body` contributes its conjuncts; `Head` is left whole.  Throws
  `:not-well-formed` when the second argument is not an `(implies …)` (docs/naf.md,
  \"`forall` is sugar for a nested `unknown`\")."
  [form]
  (let [inner (nth form 2)]
    (when-not (implies? inner)
      (throw (ex-info (str "forall quantifies " (pr-str inner)
                           ", which is not an (implies Body Head) — a universal is a"
                           " guard over the bindings its body produces, so it needs a"
                           " body to range over and a head to hold of them")
                      {:type :not-well-formed :forall form})))
    (list unknown-functor
          (list there-exists-functor (second form)
                (apply list and-functor
                       (conj (vec (rule-antecedents inner))
                             (list unknown-functor (rule-consequent inner))))))))

(defn exception-conjuncts
  "Normalize an `exceptWhen` query to its one internal shape — a vector of literals,
  *all* of which must hold.  A conjunction is written as a vector, the way
  `core/prove` spells one; a single literal may be written bare.

  A `forall` conjunct is the nested NAF it is (`desugar-forall-literal`), as a `forall`
  antecedent is, so the re-check index and the stratification graph read the
  predicates under it.  A malformed one is left for `check-exception-closed` to refuse:
  this runs inside `peel-rule-wrapper`, which reports rather than throws."
  [form]
  (mapv #(canon (if (and (forall? %) (implies? (nth % 2))) (desugar-forall-literal %) %))
        (if (vector? form) form [form])))

(defn peel-rule-wrapper
  "Strip the virtual rule wrappers, returning
  [direction defeasible exception assumption constraint inner].  Wrappers may nest in
  any order — a defeasible forward rule with an exception, an assumption rule, a hard
  constraint — and two `exceptWhen`s conjoin.  `exception` is nil or a vector of
  literals; `assumption` is true or nil; `constraint` is `:hard` / `:soft` or nil.  A
  `set/solveRule` is stripped too, and `solve-wrapped?` reports it."
  [form]
  (loop [f form, dir nil, def? nil, exc nil, assum nil, con nil]
    (if (and (sequential? f) (seq f))
      (let [h (first f)]
        (cond
          (= h default-rule-wrapper)    (recur (second f) dir true exc assum con)
          (= h assumption-rule-wrapper) (recur (second f) dir def? exc true con)
          (constraint-rule-wrappers h)  (recur (second f) dir def? exc assum (constraint-rule-wrappers h))
          (rule-direction-wrappers h)   (recur (second f) (rule-direction-wrappers h) def? exc assum con)
          (= h solve-rule-wrapper)      (recur (second f) dir def? exc assum con)
          (and (= h except-wrapper) (= 3 (count f)))
          (recur (nth f 2) dir def? (into (or exc []) (exception-conjuncts (second f))) assum con)
          :else                         [dir def? exc assum con f]))
      [dir def? exc assum con f])))

(defn desugar-forall-rule
  "`rule-form` with every `(forall …)` antecedent replaced by `desugar-forall-literal`'s
  nested NAF.  A form with none, and a form that is not a rule, is returned unchanged.
  Called by the sentex constructor and `rules/inner-rule` (docs/naf.md)."
  [rule-form]
  (let [antes (when (implies? rule-form) (rule-antecedents rule-form))]
    (if-not (some forall? antes)
      rule-form
      (rule-sentence (mapv #(if (forall? %) (desugar-forall-literal %) %) antes)
                     (rule-consequent rule-form)))))

(defn check-exception-closed
  "Throw unless the `exceptWhen` exception is **closed** over `antecedents`: every
  free variable it reads is bound before it runs, so the rule's bindings never wait on
  the exception.  The mirror of `rules/check-range-restricted`, pointed at the
  exception instead of the consequent.

  Free as `free-vars` counts it, so a `thereExists` the exception carries binds its own
  witness — \"birds fly unless they have a sick child\" is
  `(thereExists ?c (and (childOf ?b ?c) (sick ?c)))`.  That binder must be **local**
  (`:quantifier-not-local`): one the antecedents also name would be substituted with
  the rule's binding before the query runs, leaving a quantifier over a constant."
  [antecedents exception]
  ;; a well-formed `forall` was desugared by `exception-conjuncts`; this refuses the rest
  (run! desugar-forall-literal (filter forall? exception))
  ;; `_` is an anonymous wildcard: two occurrences are two *different* variables, so
  ;; an antecedent can never bind one for the exception to read.
  (when-let [w (seq (filter #(= '_ %) (mapcat form-vars exception)))]
    (throw (ex-info (str "exception " (pr-str (vec exception)) " uses the anonymous"
                         " wildcard _, which binds nothing — two occurrences of _ are two"
                         " different variables, so no antecedent can bind one for the"
                         " exception to read.  Name the variable and bind it in an"
                         " antecedent")
                    {:type :exception-not-closed :unbound (vec w)
                     :exception (vec exception) :antecedents (vec antecedents)})))
  (let [bound  (into #{} (mapcat form-vars) antecedents)
        leaked (distinct (filter bound (mapcat quantified-vars
                                               (forms-where #(or (there-exists? %) (forall? %))
                                                            exception))))
        loose  (distinct (remove bound (mapcat free-vars exception)))]
    (when (seq leaked)
      (throw (ex-info (str "exception quantifier variable " (pr-str (vec leaked))
                           " is also a rule variable — a bound existential variable must"
                           " appear only inside its own quantifier")
                      {:type :quantifier-not-local :leaked (vec leaked)
                       :exception (vec exception) :antecedents (vec antecedents)})))
    (when (seq loose)
      (throw (ex-info (str "exception is not closed: " (pr-str (vec loose))
                           " unbound by the rule's antecedents — bind each one in an antecedent,"
                           " or take it out of the exception")
                      {:type :exception-not-closed :unbound (vec loose)
                       :exception (vec exception) :antecedents (vec antecedents)})))))

(defn check-naf-closed
  "Throw unless rule antecedents `antes` (with consequent `conseq` and exception `exc`) use
  their NAF and deferred literals soundly:

  - every free variable of an `unknown`, aggregate or other deferred literal is bound by a
    generator antecedent or by a deferred literal written before it (`:naf-not-closed`);
  - a `thereExists` binder or an aggregate's reduction variable appears nowhere outside its
    own literal (`:quantifier-not-local`);
  - a quantified variable a computed conjunct of an `unknown` query reads is produced by a
    generator conjunct of the same query (`unproducible-inputs`, `:naf-not-closed`), and an
    aggregate's local census variables are ones `census-bound-vars` reaches;
  - an `unknown` query is not an empty conjunction, and a reduction slot and every
    `thereExists`, `forall` and head `exists` binder hold a variable (`:not-well-formed`).

  See docs/naf.md, \"Fully bound to evaluate\", and docs/aggregate.md, \"Grouping\"."
  [antes conseq exc]
  (let [scope    (vec (concat antes [conseq] exc))
        ;; delayed: a rule with no quantifier never counts occurrences
        rule-occ (delay (frequencies (form-vars scope)))
        ;; "does this variable of `lit` reach the rest of the rule": locality reads it to
        ;; refuse a leak, the aggregate to tell a group variable from a local one
        escapes?
        (fn [lit]
          (let [local (frequencies (form-vars lit))]
            (fn [v] (> (get @rule-occ v 0) (get local v 0)))))
        local-check
        (fn [lit vars kind]
          (let [escapes (escapes? lit)]
            (when-let [leaked (seq (filter escapes vars))]
              (throw (ex-info (str (clojure.core/name kind) " variable " (pr-str (vec leaked))
                                   " escapes its quantifier — a bound existential"
                                   " variable must appear only inside its own "
                                   (clojure.core/name kind))
                              {:type :quantifier-not-local :leaked (vec leaked)
                               kind lit :antecedents (vec antes)})))))
        closed-check
        (fn [lit vars bound kind]
          (when-let [loose (seq (remove bound vars))]
            (throw (ex-info (str (clojure.core/name kind) " antecedent is not closed: "
                                 (pr-str (vec loose))
                                 " unbound by anything else in the rule — it"
                                 " consumes bindings rather than producing them, so its"
                                 " inputs must be bound first")
                            {:type :naf-not-closed :unbound (vec loose)
                             kind lit :antecedents (vec antes)}))))
        ;; an aggregate's inputs are its group variables: the body's free variables the
        ;; rest of the rule also names
        aggregate-inputs
        (fn [ag] (filter (escapes? ag) (deferred-input-vars ag)))
        census-check
        ;; ...and the local ones must be bound by the census body itself; the `unknown`
        ;; half of this rule is `unproducible-inputs`
        (fn [ag]
          (let [body    (aggregate-body ag)
                escapes (escapes? ag)
                bound   (census-bound-vars body)]
            (when-let [loose (seq (distinct (remove #(or (escapes %) (bound %))
                                                    (free-vars body))))]
              (throw (ex-info (str "aggregate census " (pr-str body) " reads "
                                   (pr-str (vec loose))
                                   ", which no conjunct of it binds and nothing outside"
                                   " the aggregate names — a census variable is bound by"
                                   " a generator conjunct of the body or by an earlier"
                                   " antecedent, and this is neither")
                              {:type :naf-not-closed :unbound (vec loose) :aggregate ag
                               :antecedents (vec antes)})))))]
    ;; binders and locality, in one walk over every quantifier shape
    (let [quantifiers (forms-where #(or (there-exists? %) (forall? %) (head-exists? %)
                                        (aggregate? %))
                                   scope)]
      (run! check-binder (remove aggregate? quantifiers))
      (doseq [te (filter there-exists? quantifiers)]
        (local-check te (quantified-vars te) :thereExists))
      (doseq [ag (filter aggregate? quantifiers)]
        (if-let [v (aggregate-value-var ag)]
          (do (local-check ag #{v} :aggregate)
              (census-check ag))
          (throw (ex-info (str "aggregate reduces over " (pr-str (nth ag 2))
                               ", which is not a variable — the second slot names the"
                               " value being reduced, so a constant there reduces over"
                               " nothing and no prover can answer it")
                          {:type :not-well-formed :aggregate ag
                           :antecedents (vec antes)})))))
    (doseq [unk (filter unknown? antes)]
      (when (empty? (naf-query-conjuncts unk))
        (throw (ex-info (str "unknown antecedent " (pr-str unk) " queries an empty"
                             " conjunction, which nothing can make derivable — so the"
                             " unknown always holds and the antecedent guards nothing")
                        {:type :not-well-formed :unknown unk
                         :antecedents (vec antes)})))
      (when-let [loose (seq (distinct (unproducible-inputs (second unk))))]
        (throw (ex-info (str "unknown antecedent " (pr-str unk) " reads "
                             (pr-str (vec loose))
                             " in a computed conjunct that nothing in the query binds —"
                             " a quantified variable is bound by a generator conjunct of"
                             " the same query, and no other conjunct can supply it")
                        {:type :naf-not-closed :unbound (vec loose) :unknown unk
                         :antecedents (vec antes)}))))
    ;; closure, scanned left to right so a deferred literal's outputs count only after it
    (when (some #(or (unknown? %) (deferred-literal? %)) antes)
      (let [generators (remove #(or (unknown? %) (deferred-literal? %)) antes)
            matched    (into #{} (mapcat form-vars) generators)]
        (reduce (fn [bound a]
                  (if (or (unknown? a) (deferred-literal? a))
                    (do (closed-check a
                                      (if (aggregate? a)
                                        (aggregate-inputs a)
                                        (deferred-input-vars a bound))
                                      bound
                                      (cond (unknown? a)   :unknown
                                            (aggregate? a) :aggregate
                                            :else          :deferred))
                        (into bound (deferred-output-vars a bound)))
                    bound))
                matched
                antes)))
    nil))

(defn- fold-comparison
  "Fold a comparison onto its canonical sibling by reversing the arguments —
  (greaterThan a b c) ⇒ (lessThan c b a).  A dotted-rest form is left alone: its
  arguments are a splice, not a positional list."
  [form]
  (if-let [sib (and (sequential? form) (seq form)
                    (not (dotted? form))
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

;; Genuine in-file cycle, and the structure of the data: `cmp-term` on a compound descends to
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

;; ---- quoting functions ---------------------------------------------------

(def quote-functor
  "The quoting function whose argument is a form taken as syntax: `(Quote X)` mentions X.
  `quasiquote/quote-function` is this symbol."
  'Quote)

(def quasiquote-functor
  "The template-constructing quoting function: `(Quasiquote T)` mentions T with its
  `(Unquote v)` holes spliced.  `quasiquote/quasiquote-function` is this symbol."
  'Quasiquote)

(def quoting-functors
  "The quoting functions — `Quote` and `Quasiquote`, fixed by the engine.  A quoting
  function's arguments are a **mention**, a term named as syntax rather than used: they are
  held opaque to identity congruence (`res/representative-term` rewrites them by a
  `rewriteOf` spelling rename only, never by a `sameAs` / `equals` merge), not reified on
  their own when the application is (`nat/reify-or-mint-nat`), and not typed by what they
  denote (`checks`).  The set is not declared in the KB and no assertion changes it, so
  whether an argument is a mention is a fact about the sentence alone."
  #{quote-functor quasiquote-functor})

(defn quoting-functor?
  "Is `head` one of the `quoting-functors`?"
  [head]
  (contains? quoting-functors head))

(defn quote-form?
  "Is `form` a `(Quote X)` mention?  `unquoted-free-vars`, `res/unify`, `res/substitute`
  and the literal cache's renaming all read a form this answers true for as a constant."
  [form]
  (and (sequential? form) (= quote-functor (first form)) (= 2 (count form))))

;; ---- symmetric arguments -------------------------------------------------

(defn ground-term?
  "True when `t` contains no pattern variable anywhere."
  [t]
  (not (some-symbol? variable? t)))

(defn sortable-term?
  "True when `t` holds no pattern variable outside a `(Quote …)`.  A quoted form is a
  constant (`quote-form?`), so the permuting sorts order a term whose only variables are
  quoted as they order a ground one: `(RulePairFn (Quote r1) (Quote r2))` over two quoted
  rules sorts under `(commutative RulePairFn)`."
  [t]
  (cond (quote-form? t) true
        (sequential? t) (every? sortable-term? t)
        :else           (not (variable? t))))

(defn form-variables
  "Every variable anywhere in `form`, as a set — `#{}` rather than `symbols-where`'s nil,
  since every caller folds the answer into something or calls it as a fn.  The one set
  walk: `resolution`, `plan`, `quality`, `provers` and `asp.solve-context` call it."
  [form]
  (or (symbols-where variable? form) #{}))

(defn symmetric-literal?
  "A binary literal whose predicate is declared symmetric (and not a dotted form)."
  [form symmetric?]
  (boolean (and (sequential? form) (= 3 (count form)) (symbol? (first form))
                (not (dotted? form))
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
           (every? sortable-term? (rest form)))
    (let [[p x y] form]
      (if (pos? (cmp-term x y)) (list p y x) form))
    form))

(defn mirror-literal
  "The argument-swapped twin of a binary literal, for symmetric lookup."
  [form]
  (let [[p x y] form] (list p y x)))

;; ---- commuting argument groups -------------------------------------------
;;
;; `symmetric` above commutes the two arguments of a binary predicate.  The three
;; commutativity marks generalize that to a declared set of positions at any arity, and
;; reduce to one runtime descriptor the functions below read:
;;
;;   [:rest f]        every position from f to the literal's own arity — the runtime form
;;                    of `(commutativeInArgAndRest P f)`, and of `(commutative P)`, whose
;;                    own arm installs `[:rest 1]` (`special/arms`)
;;   [:args [p …]]    exactly the named positions — `(commutativeInArgs P p1 p2 …)`
;;
;; Positions are 1-based over the arguments, so position 1 is `(second form)`.  The
;; descriptors come from the KB (`taxonomy/commuting-groups`); everything here is pure,
;; so a KB-free construction permutes nothing.

(defn- group-positions
  "The positions one group descriptor names at runtime arity `arity`, as a sorted vector.
  A `:rest` group is open-ended, so the literal's own arity is what closes it — which is
  how two runtime arities of a variable-arity predicate stay two claims rather than one:
  each gets its own position set, and a permutation never moves an argument across them."
  [[kind v] arity]
  (case kind
    :rest (vec (range (max 1 (long v)) (inc arity)))
    :args (vec (sort (distinct (filter #(<= 1 (long %) arity) v))))))

(defn commuting-components
  "The components `groups` licences at runtime arity `arity`: sorted position vectors,
  themselves in sorted order, each holding at least two positions.  Overlapping groups merge
  into connected components, since `(commutativeInArgs P 1 2)` beside `(commutativeInArgs P 2
  3)` makes 1 and 3 interchange and applying the two separately would depend on order.  A
  component of one position is dropped, so a mark whose positions fall outside the literal's
  arity leaves the literal alone."
  [groups arity]
  (when (and (seq groups) (pos? arity))
    (let [sets (into [] (comp (map #(group-positions % arity))
                              (filter #(> (count %) 1))
                              (map set))
                     groups)]
      (when (seq sets)
        (loop [[x & more] sets, done []]
          (if (nil? x)
            (not-empty (vec (sort-by first (map (comp vec sort) done))))
            ;; merge `x` with every component it touches, then carry the union forward
            (let [touches? (fn [c] (boolean (some c x)))
                  hit      (filterv touches? done)
                  miss     (filterv (complement touches?) done)]
              (recur more (conj miss (reduce into x hit))))))))))

(defn- sort-commuting-args
  "Put the arguments of a **fully ground** literal into canonical order within each commuting
  component, so every permitted permutation of a fact stores as one sentex.  Positions outside
  a component keep their slot.  `groups-of` is `(fn [functor arity] -> groups)`; a predicate
  declaring nothing answers nil and the literal is returned untouched.

  The declaration read comes before the groundness walk, since this runs on every literal
  `assert` canonicalizes (as in `sort-symmetric-args`).  Ground literals only: a pattern's
  variables sort last, and `res/raw-match` fans a pattern over its arrangements instead.
  Repeats keep their multiplicity."
  [form groups-of]
  (if-not (and (sequential? form) (symbol? (first form)) (next form))
    form
    (let [args  (vec (rest form))
          comps (commuting-components (groups-of (first form) (count args)) (count args))]
      (if-not (and comps
                   (not (dotted? form))
                   (every? sortable-term? args))
        form
        (let [args' (reduce (fn [acc positions]
                              (let [sorted (sort cmp-term (map #(nth acc (dec %)) positions))]
                                (reduce (fn [a [pos t]] (assoc a (dec pos) t))
                                        acc
                                        (map vector positions sorted))))
                            args
                            comps)]
          (if (= args' args) form (apply list (first form) args')))))))

(defn- ordered-slot-choices
  "Every way to place `k` distinguishable items into `n` slots, as vectors of `k` distinct
  slot indices — the ordered selections, `n!/(n-k)!` of them.  `[[]]` for `k` of 0."
  [n k]
  (if (zero? k)
    [[]]
    (reduce (fn [acc _]
              (into [] (for [prefix acc
                             i      (range n)
                             :when  (not (some #(= i %) prefix))]
                         (conj prefix i))))
            [[]]
            (range k))))

(defn- cartesian
  "The cartesian product of a sequence of collections, as a lazy sequence of vectors."
  [colls]
  (if (empty? colls)
    [[]]
    (for [x (first colls) more (cartesian (rest colls))] (into [x] more))))

(defn- component-arrangements
  "Every argument list the terms `ts` of one commuting component may be probed under,
  with the ground terms held in sorted order.  See `commuting-arrangements`."
  [ts]
  (let [vars   (filterv (complement sortable-term?) ts)
        consts (vec (sort cmp-term (filterv sortable-term? ts)))
        n      (count ts)]
    (mapv (fn [slots]
            (let [at (zipmap slots vars)]
              (loop [i 0, cs consts, out []]
                (if (= i n)
                  out
                  (if-let [v (find at i)]
                    (recur (inc i) cs (conj out (val v)))
                    (recur (inc i) (rest cs) (conj out (first cs))))))))
          (ordered-slot-choices n (count vars)))))

(defn arrangements-over
  "`commuting-arrangements` against components already in hand — the form a caller takes
  when it knows the components from somewhere other than the literal's own functor.

  Forward chaining is that caller: a datum arrives and the rule antecedent it is matched
  against may name a **super-predicate** of the datum's functor, while what licences the
  permutation is the datum's own declaration (`chain/symmetric-mirror` states the same
  rule for the binary case).  So the components come off the fact and the arrangements
  are built over the antecedent."
  [form comps]
  (if-not (and (sequential? form) (symbol? (first form)) (next form)
               comps
               (not (dotted? form)))
    [form]
    (let [args     (vec (rest form))
          comps    (filterv #(every? (fn [p] (<= p (count args))) %) comps)
          per-comp (mapv (fn [positions]
                           (component-arrangements
                            (mapv #(nth args (dec %)) positions)))
                         comps)]
      (if (empty? comps)
        [form]
        (into []
              (distinct)
              (cons form
                    (map (fn [choice]
                           (apply list (first form)
                                  (reduce (fn [acc [positions ts]]
                                            (reduce (fn [a [pos t]] (assoc a (dec pos) t))
                                                    acc (map vector positions ts)))
                                          args
                                          (map vector comps choice))))
                         (cartesian per-comp))))))))

(defn commuting-arrangements
  "Every rearrangement of `form` a lookup has to probe for, given the components `groups-of`
  licences at this literal's arity.  `form` is first; a literal that commutes nothing yields
  only itself.

  Pruned to the arrangements a stored fact can have: storage sorts a ground literal within
  each component (`sort-commuting-args`), unification is positional, and a sorted sequence
  read at a subset of its slots is sorted.  This relies on stored facts being canonical under
  the declaration, which `integrate/commute-existing` maintains.  With `v` variables among a
  component of `g` positions the probes number `g!/(g-v)!` and not `g!`.  Where the fan is
  factorial the answer set is too (`res/raw-match`).  Distinct by form, so `(P ?a ?a)` is one
  probe."
  [form groups-of]
  (if-not (and (sequential? form) (symbol? (first form)) (next form))
    [form]
    (arrangements-over form
                       (commuting-components (groups-of (first form) (dec (count form)))
                                             (dec (count form))))))

(defn- sort-conjunction
  "One conjunction in canonical order: each conjunct rewritten by `f`, then sorted blind
  to variable names, repeats dropped, a lone conjunct unwrapped.  The conjuncts `held?`
  names follow the sorted rest in their written order.  Nil when there is nothing to
  rewrite (the form is not a conjunction, or is the empty one `check-naf-closed` refuses
  — rewriting that would erase the form the diagnostic names)."
  [body f held?]
  (when (conjunction? body)
    (let [cs (map f (conjuncts body))
          cs (vec (distinct (concat (sort cmp-blind (remove held? cs)) (filter held? cs))))]
      (cond
        (empty? cs)      nil
        (= 1 (count cs)) (first cs)
        :else            (apply list and-functor cs)))))

(defn- sort-query-conjunctions
  "`form`, an `unknown` or `thereExists` form, with every conjunction in it in
  `sort-conjunction`'s canonical order: its own query's, and those of an `unknown` or
  `thereExists` conjunct at any depth (a `forall` head is one), the conjuncts `held?`
  names last in their written order.  Any other form is unchanged."
  [form held?]
  (letfn [(nested [c]
            (cond (unknown? c)      (list unknown-functor (query (second c)))
                  (there-exists? c) (list there-exists-functor (second c) (query (nth c 2)))
                  :else             c))
          (query [q] (or (sort-conjunction q nested held?) (nested q)))]
    (nested form)))

(defn- sort-naf-conjuncts
  "`form`, an `unknown` antecedent, with every conjunction in its query in canonical
  order (`sort-query-conjunctions`); any other form unchanged.  Blind to variables,
  unlike `sort-conjuncts`, because this runs on the surface literal before the rule's
  variables are numbered; `naf-numberings` breaks the ties it leaves (docs/naf.md,
  \"`S` may be a conjunction\")."
  [form]
  (if (unknown? form) (sort-query-conjunctions form (constantly false)) form))

(defn- elim-double-not
  "Eliminate double negation from a literal: an even count of leading `not`s becomes the
  bare body, an odd count one `not`.  The fact entry point does this through `peel-not`; the
  rule entry point must too, or `(not (not (foo ?x)))` normalizes unchanged, keys under
  `[:not not]` (`rules/antecedent-key`), and — since a stored fact canonicalizes that
  key away to `(foo ?x)` — nothing ever triggers the rule, which is then silently inert."
  [form]
  (let [[polarity body] (peel-not form)]
    (if (= polarity :negative) (list 'not body) body)))

(defn permute-args
  "`form`'s own arguments in the order its permuting marks give a ground application: the
  symmetric sort, then the commuting sort.  The literal, every compound below it
  (`canonical-args`) and the expression a reified constant is named by
  (`nat-read/sorted-expression`) take their argument order from this one list of arms."
  [form {:keys [symmetric? groups-of]}]
  (-> form (sort-symmetric-args symmetric?) (sort-commuting-args groups-of)))

(defn- held-as-written?
  "Does the application `form` keep its arguments as written: a quoting functor's
  argument, which is a mention, or a functor `opaque?` names?"
  [form opaque?]
  (let [f (first form)] (or (quoting-functor? f) (boolean (opaque? f)))))

(defn- absorb-args
  "`args` less every argument another argument lies `below?`, keeping of two arguments
  below each other the `cmp-term`-least, and of two equal ones the first.  Over a
  preorder this keeps one argument of each minimal class."
  [args below?]
  (let [v (vec args)
        n (count v)]
    (into [] (keep-indexed
              (fn [i x]
                (when-not (some (fn [j]
                                  (let [y (v j)]
                                    (and (not= i j) (below? y x)
                                         (or (not (below? x y))
                                             (let [c (cmp-term y x)]
                                               (or (neg? c) (and (zero? c) (< j i))))))))
                                (range n))
                  x)))
          v)))

(defn- canonical-term
  "A compound below the literal in canonical form: `permute-args`' order, and for a ground
  application of a function the term marks name, four arms more.  An `associative?`
  functor's arguments that apply it are spliced in, before the sort.  An `idempotent?`
  one drops an argument equal to its neighbour after the sort when it is associative too,
  and otherwise only collapses an application whose arguments are all equal.  A functor
  for which `meet-order` gives a comparator drops an argument another lies below
  (`absorb-args`).  One `distinct-from` gives `n` drops a repeat from position `n` on and
  keeps its functor; an idempotent or meet one left with one argument is that argument."
  [form {:keys [associative? idempotent? meet-order distinct-from] :as marks}]
  (let [f      (first form)
        a?     (boolean (and associative? (associative? f)))
        i?     (boolean (and idempotent? (idempotent? f)))
        below? (when meet-order (meet-order f))
        from   (when distinct-from (distinct-from f))]
    (if-not (and (or a? i? below? from) (symbol? f) (next form)
                 (not (dotted? form))
                 (every? ground-term? (rest form)))
      (permute-args form marks)
      (let [spliced  (if a?
                       (mapcat #(if (and (seq? %) (= f (first %))) (rest %) [%]) (rest form))
                       (rest form))
            sorted   (rest (permute-args (apply list f spliced) marks))
            deduped  (cond (not i?)              sorted
                           a?                    (dedupe sorted)
                           (apply = sorted)      [(first sorted)]
                           :else                 sorted)
            absorbed (if below? (absorb-args deduped below?) deduped)
            args     (if from
                       (let [k (dec (long from))]
                         (concat (take k absorbed) (distinct (drop k absorbed))))
                       absorbed)]
        (cond
          (and (= 1 (count args)) (or i? below?)) (first args)
          (= args (rest form))                    form
          :else                                   (apply list f args))))))

(defn- mention-at-fn
  "`marks`' `:mention-at?`, `(fn [functor position])`, or one answering false."
  [{:keys [mention-at?]}]
  (or mention-at? (constantly false)))

(defn- canonical-args
  "`form` with every compound argument, at any depth, in the form `canonical-term` gives
  it, innermost first, so an arm above compares canonical subterms.  The walk enters list
  forms only, and stops at an application `held-as-written?` and at a position
  `:mention-at?` names.  `form` itself is returned when nothing below it moved."
  [form {:keys [opaque?] :as marks}]
  (let [compound? #(and (seq? %) (seq %))]
    (if (or (not (compound? form))
            (not-any? compound? (rest form))
            (held-as-written? form opaque?))
      form
      (let [args     (rest form)
            mention? (mention-at-fn marks)
            args'    (into [] (map-indexed
                               (fn [i a]
                                 (if (and (compound? a) (not (held-as-written? a opaque?))
                                          (not (mention? (first form) (inc i))))
                                   (canonical-term (canonical-args a marks) marks)
                                   a)))
                           args)]
        (if (every? true? (map identical? args args'))
          form
          (apply list (first form) args'))))))

(defn canonical-subterm
  "Term `t` in the form the store holds it in as an argument (`canonical-args`): a compound
  not `held-as-written?` with its own and every inner application in canonical form, any
  other term itself.  `marks` is `sentex`'s canonicalization reads."
  [t {:keys [opaque?] :as marks}]
  (if (and (seq? t) (seq t) (not (held-as-written? t opaque?)))
    (canonical-term (canonical-args t marks) marks)
    t))

(defn- open-compound?
  "Is `t` a list compound holding a variable outside a `(Quote …)`: one a store holds in
  an argument order a pattern cannot be sorted into?"
  [t]
  (and (seq? t) (seq t) (not (sortable-term? t))))

(defn- own-arrangements
  "The argument orders compound `t` is probed in under its own functor's permuting marks:
  its pruned commuting arrangements (`commuting-arrangements`) and, for a symmetric binary
  application, its mirror.  `t` first."
  [t {:keys [symmetric? groups-of]}]
  (cond-> (commuting-arrangements t (or groups-of (constantly nil)))
    (and symmetric? (symmetric-literal? t symmetric?)) (-> (conj (mirror-literal t)) distinct vec)))

(defn nested-arrangements
  "Every spelling of literal `form` a lookup probes for the compounds below it: each
  compound holding a variable, at any depth, in each argument order its own functor's
  permuting marks let a stored fact hold it in (`own-arrangements`), innermost first.
  `form` is first, and its own arguments keep their order, which `res/raw-match-with`
  fans.  Under a `not` the body's arguments keep theirs.  The walk stops where
  `canonical-args` does.  `[form]` when no argument is an open compound."
  [form {:keys [opaque?] :as marks}]
  (letfn [(mention? [f i] ((mention-at-fn marks) f i))
          (term [t]
            (if (and (open-compound? t) (not (held-as-written? t opaque?)))
              (into [] (comp (mapcat #(own-arrangements % marks)) (distinct)) (args-of t))
              [t]))
          (args-of [t]
            (let [alts (into [] (map-indexed
                                 (fn [i a] (if (and (open-compound? a) (mention? (first t) (inc i))) [a] (term a))))
                             (rest t))]
              (if (every? #(= 1 (count %)) alts)
                [t]
                (map #(apply list (first t) %) (cartesian alts)))))
          (below [f]
            (if (and (seq? f) (some open-compound? (rest f)) (not (held-as-written? f opaque?)))
              (into [] (distinct) (args-of f))
              [f]))]
    (if (and (seq? form) (= not-functor (first form)) (= 2 (count form)))
      (mapv #(list not-functor %) (below (second form)))
      (below form))))

(defn every-order
  "Every argument order compound `t` may have been written in under its own functor's
  permuting marks: each permutation within each commuting component, or the mirror of a
  symmetric binary application.  `t` first."
  [t {:keys [symmetric? groups-of]}]
  (let [args  (vec (rest t))
        n     (count args)
        comps (or (commuting-components ((or groups-of (constantly nil)) (first t) n) n)
                  (when (and symmetric? (symmetric-literal? t symmetric?)) [[1 2]]))]
    (into [] (distinct)
          (cons t (for [choice (cartesian (mapv #(ordered-slot-choices (count %) (count %)) comps))]
                    (apply list (first t)
                           (reduce (fn [acc [ps slots]]
                                     (reduce (fn [a [i s]] (assoc a (dec (nth ps s)) (nth args (dec (nth ps i)))))
                                             acc (map-indexed vector slots)))
                                   args (map vector comps choice))))))))

(defn mention-arrangements
  "Every spelling of literal `form` a fact may be stored under at a mention position
  `split?` names (`(fn [functor position])`): each compound there, and every compound
  inside it, in every argument order its own functor's permuting marks allow
  (`every-order`).  The walk descends where `canonical-args` does.  `form` first, and
  `[form]` when no such position holds a compound."
  [form {:keys [opaque?] :as marks} split?]
  (letfn [(compound? [t] (and (seq? t) (seq t) (not (held-as-written? t opaque?))))
          (orders [t]
            (if (compound? t)
              (into [] (comp (mapcat #(every-order % marks)) (distinct))
                    (map #(apply list (first t) %) (cartesian (mapv orders (rest t)))))
              [t]))
          (walk [t]
            (if (compound? t)
              (let [alts (into [] (map-indexed
                                   (fn [i a]
                                     (cond (not (compound? a))                      [a]
                                           (not ((mention-at-fn marks) (first t) (inc i))) (walk a)
                                           (split? (first t) (inc i))                (orders a)
                                           :else                                    [a])))
                               (rest t))]
                (if (every? #(= 1 (count %)) alts)
                  [t]
                  (mapv #(apply list (first t) %) (cartesian alts))))
              [t]))]
    (if (and (seq? form) (= not-functor (first form)) (= 2 (count form)))
      (mapv #(list not-functor %) (walk (second form)))
      (walk form))))

(defn reader-arrangements
  "Every spelling of literal `form` with each compound below the literal that applies a
  functor in the set `fs`, ground or open, in every argument order its marks allow
  (`every-order`), innermost first: the spellings a reader that does not believe those
  marks may hold a fact in.  The literal's own arguments keep their order, and the walk
  descends where `canonical-args` does.  `form` first, and `[form]` when no compound
  below it applies one."
  [form {:keys [opaque?] :as marks} fs]
  (letfn [(compound? [t] (and (seq? t) (seq t) (not (held-as-written? t opaque?))))
          (args-of [t]
            (let [alts (into [] (map-indexed
                                 (fn [i a] (if (and (compound? a) (not ((mention-at-fn marks) (first t) (inc i))))
                                             (walk a)
                                             [a])))
                             (rest t))]
              (if (every? #(= 1 (count %)) alts)
                [t]
                (mapv #(apply list (first t) %) (cartesian alts)))))
          (walk [t]
            (if (contains? fs (first t))
              (into [] (comp (mapcat #(every-order % marks)) (distinct)) (args-of t))
              (args-of t)))]
    (cond
      (and (seq? form) (= not-functor (first form)) (= 2 (count form)) (compound? (second form)))
      (mapv #(list not-functor %) (into [] (distinct) (args-of (second form))))
      (compound? form) (into [] (distinct) (args-of form))
      :else [form])))

(defn sort-compounds
  "`form` with every compound below it in the argument order the store gives a ground
  one (`canonical-args`), and its own arguments as written.  A pattern's ground subterms
  are matched in this spelling, since a stored fact holds them in it.  `marks` is
  `sentex`'s canonicalization reads."
  [form marks]
  (canonical-args form marks))

(defn compound-functors
  "The functors whose permuting marks spell `form` (`canonical-args`): its own, and the
  functor of every list compound below it that the walk enters.  A set; atoms only."
  [form opaque?]
  (letfn [(heads [acc t]
            (if (and (seq? t) (seq t) (not (held-as-written? t opaque?)))
              (reduce heads (cond-> acc (symbol? (first t)) (conj (first t))) (rest t))
              acc))]
    (if (and (seq? form) (seq form))
      (reduce heads (cond-> #{} (symbol? (first form)) (conj (first form))) (rest form))
      #{})))

(defn normalize-literal
  "One literal in canonical form.  `marks` carries the KB reads canonicalization makes —
  `:symmetric?`, whether a functor is declared symmetric, `:groups-of`, the commutativity
  groups it declares at a given arity, `:opaque?`, whether an application of a functor
  keeps its arguments as written, `:mention-at?`, whether a functor's argument position is
  kept as written, and the term marks `canonical-term` reads below the literal
  (`:associative?`, `:idempotent?`, `:meet-order`, `:distinct-from`).  Each defaults to
  answering nothing, so a KB-free construction reorders no arguments.  The compounds below
  the literal are put in canonical form first (`canonical-args`), then the literal's own
  arguments in order."
  [form marks]
  (-> form elim-double-not fold-comparison sort-naf-conjuncts
      (canonical-args marks)
      (permute-args marks)))

;; ---- chained comparisons collapse into one variable-arity literal -------

(defn- collapse-comparison-chains
  "Merge chained comparisons among `lits` into single variable-arity literals:
  (lessThan a b) + (lessThan b c) ⇒ (lessThan a b c).  Only a simple chain merges —
  a branch (a<b, a<c) is left alone."
  [lits]
  (let [chain? #(and (sequential? %) (contains? chained-comparisons (first %))
                     (>= (count %) 3) (not (dotted? %)))
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
  variable → its canonical name, `:vm` the inverse (the `:varmap` a sentex carries).
  A numbering inside a `thereExists` also holds `:pool`, its binder's variables → the
  block reserved for them, and `:free`, each block's names not yet taken
  (`naf-numberings`)."
  {:n 0 :m {} :vm {}})

(defn- number-form
  "Number every variable in `form` to ?var0, ?var1, … by first occurrence, continuing
  the numbering `st`.  Each anonymous `_` gets its own fresh, unshared name (two
  occurrences are two different variables).  A variable in `:pool` takes the lowest
  name left in its reserved block instead of `:n`.  Returns [numbered-form st']."
  [st form]
  (let [state (volatile! st)
        fresh (fn [orig]
                (let [{:keys [n vm]} @state
                      v (intern-sym (symbol (str "?var" n)))]
                  (vswap! state assoc :n (inc n) :vm (assoc vm v orig))
                  v))
        reserved (fn [orig k]
                   (let [[v & more] (get-in @state [:free k])]
                     (vswap! state #(-> % (assoc-in [:free k] (vec more))
                                        (update :vm assoc v orig)))
                     v))]
    (letfn [(rn [x]
              (cond
                (and (symbol? x) (= "_" (clojure.core/name x))) (fresh x)
                (variable? x) (or (get (:m @state) x)
                                  (let [k (get (:pool @state) x)
                                        v (if k (reserved x k) (fresh x))]
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
  A state is `{:order [numbered-literal …] :st <numbering> :left [author-literal …]}`.
  `number` is `minimal-orders`'s, and `relevant` the variables that occur after the
  group."
  [states number relevant]
  (let [exts (vec (for [{:keys [order st left] :as s} states
                        i (range (count left))
                        :let [left' (into (subvec left 0 i) (subvec left (inc i)))]
                        [r st'] (number st (nth left i)
                                        (delay (into relevant (mapcat form-vars) left')))]
                    [r (assoc s :order (conj order r)         ; assoc, not a fresh map, so a
                              :st st'                          ; carried tag (:origin) survives
                              :left left')]))
        best (reduce (fn [a b] (if (neg? (cmp-term (first b) (first a))) b a)) exts)]
    (into [] (comp (filter #(zero? (cmp-term (first %) (first best))))
                   (map second)
                   (distinct))
          exts)))

(defn- suffix-vars
  "For each tie group, the author variables that still occur *after* it — in the later
  groups and in `base`, the variables of the forms numbered after the groups (the
  held-back literals, the consequent).  Two survivors that agree on those are
  interchangeable from there on, whatever they did with the variables nobody mentions
  again, so this is what collapses the survivor set between groups."
  [groups base]
  (let [acc  (reduce (fn [a g] (conj a (into (peek a) (mapcat form-vars) g)))
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
  "For each tie group, whether `prune-by-tail` may bound it.  Both conditions are needed for
  the tail projection to be exact and independent of author order:

  - joinless: no variable occurs in two of the group's literals, so every ordering renders
    the same antecedent block;
  - tail-isolated: none of the group's variables occurs in another antecedent, so the
    consequent, a never-reordered form, is the whole tiebreak.

  A group that fails either stays on the exact `extend-minimally` search.  `outside` is the
  variables of every form outside the groups but the projected tail."
  [groups outside]
  (let [gvars (mapv #(into #{} (mapcat form-vars) %) groups)
        else  (fn [i] (reduce into outside
                              (keep-indexed (fn [j vs] (when (not= i j) vs)) gvars)))
        joinless? (fn [g] (let [vs (mapcat seq (literal-var-sets g))]
                            (or (empty? vs) (apply distinct? vs))))]
    (mapv (fn [i g] (and (or (<= (count g) 1) (joinless? g))
                         (not-any? (else i) (nth gvars i))))
          (range (count groups)) groups)))

(defn- prune-by-tail
  "Break an antecedent tie by the tail, for a joinless, tail-isolated group
  (`pruneable-groups`).  Every ordering of such a group renders the same antecedents, so
  `cmp-render` decides on `proj-forms`, the consequent.  Project it under each survivor's
  partial numbering (an unnumbered variable is a sentinel that sorts last), keep the survivors
  whose projection is minimal, and collapse any left interchangeable on the projected
  variables.

  This keeps O(k²) states instead of k!, and it is exact: numbering is monotonic across
  rounds, so a survivor whose projection is larger at the first differing position is larger
  in the final rendering and cannot be the whole-rule minimum.  `keep-min` ranks survivors by
  the tail, grouped by `[:origin :order]`, since survivors from different origins differ on an
  earlier group's antecedents.  The dedup merges only survivors interchangeable on `relevant`,
  every variable that recurs downstream (`prune-survivors`), never on the tail alone."
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

(defn- number-each
  "Extend every `{:order :st}` in `states` by `forms` in order, each numbered by `number`
  (`minimal-orders`'s) under the delay `(later-of j)` of the variables after form `j`.
  A form with several minimal numberings multiplies the states."
  [states forms number later-of]
  (reduce (fn [ss j]
            (into [] (distinct)
                  (for [{:keys [order st] :as s} ss
                        [r st'] (number st (nth forms j) (later-of j))]
                    (assoc s :order (conj order r) :st st'))))
          states
          (range (count forms))))

(defn- minimal-orders
  "Every ordering of the tie `groups` whose canonically numbered literal vector is
  lexicographically minimal, numbered on from `st0`: the candidates the whole-rule tie-break
  chooses between.  `later` is the variables of the forms numbered after the groups; they
  decide which survivors still differ.  `number` numbers one literal, `(fn [st form
  later-delay])`, returning every minimal `[numbered st']` (`naf-numberings`).

  Prefix minimization is exact: a prefix's numbering depends only on that prefix and
  `cmp-literals` is lexicographic.  A distinguishable tie group collapses to one survivor at
  the first shared variable, so k literals cost O(k²) numberings.  A joinless, tail-isolated
  group (`pruneable-groups`, `outside`) is bounded by `prune-by-tail` over the consequent
  `proj-forms`."
  [st0 groups later outside proj-forms number]
  ;; `after` / `eligible` are only consulted when a group ties or a NAF literal is
  ;; numbered, so they are computed on demand
  (let [after (delay (suffix-vars groups later))]
    (if (every? #(= 1 (count %)) groups)
      ;; nothing tied: one ordering, numbered straight through.  This is the overwhelming
      ;; majority of rules, and it must not pay for the search.
      (number-each [{:order [] :st st0}] (mapv first groups) number #(delay (nth @after %)))
      (let [eligible (delay (pruneable-groups groups outside))]
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
                                (recur (prune (extend-minimally ss number relevant)) (dec k))))
                         ss (mapv #(dissoc % :left :origin) ss)]
                     [(if (next ss) (prune-survivors ss relevant) ss) (inc i)]))
                 [[{:order [] :st st0}] 0]
                 groups))))))

(defn- naf-numberings
  "Every minimal numbering of `form` continuing `st`, as `[[numbered st'] …]`: one
  numbered form, and one numbering per survivor that still differs on the variables
  `later` (a delay) names.  An `unknown` or `thereExists` form's conjunction is ordered
  by `minimal-orders` from `st`, so conjuncts `sort-naf-conjuncts` left tied are broken
  by the rule's canonical numbering as the antecedents are; any other form takes
  `number-form`.  A `thereExists` binder is a set: its variables are reserved the next
  block of numbers and take them by first occurrence in the body, and the binder is
  rendered in number order, a lone variable bare.  The conjuncts `held?` names are not
  reordered: they follow the rest of their conjunction in the order `form` holds them."
  ([st form later] (naf-numberings st form later (constantly false)))
  ([st form later held?]
   (cond
     (unknown? form)
     (for [[q st'] (naf-numberings st (second form) later held?)]
       [(list unknown-functor q) st'])

     (there-exists? form)
     (let [b   (second form)
           vs  (vec (distinct (if (sequential? b) b [b])))
           n0  (long (:n st))
           st1 (-> st
                   (assoc :n (+ n0 (count vs)))
                   (update :pool merge (zipmap vs (repeat n0)))
                   (assoc-in [:free n0] (mapv #(intern-sym (symbol (str "?var" (+ n0 (long %)))))
                                              (range (count vs)))))]
       (for [[q st2] (naf-numberings st1 (nth form 2) later held?)
             ;; a binder variable the body never names takes a name left in the block
             :let [[bs st3] (number-forms st2 vs)
                   bs       (sort cmp-term bs)]]
         [(list there-exists-functor (if (next bs) (apply list bs) (first bs)) q)
          (-> st3 (update :pool #(apply dissoc % vs)) (update :free dissoc n0))]))

     (and (conjunction? form) (next form))
     (let [number  #(naf-numberings %1 %2 %3 held?)
           defs    (filterv held? (rest form))
           dvars   (into #{} (mapcat form-vars) defs)
           later'  (into @later dvars)
           outside (into later' (keys (:m st)))
           tails   (suffix-vars (mapv vector defs) @later)]
       (for [{:keys [order st]} (-> (minimal-orders st (tie-groups (filterv (complement held?) (rest form)))
                                                    later' outside [] number)
                                    (number-each defs number #(delay (nth tails %))))]
         [(apply list and-functor order) st]))

     :else [(number-form st form)])))

(defn canonical-exception
  "An `exceptWhen` exception's conjuncts, already in the rule's canonical variables
  `rule-vars`, in their stored form: sorted (`sort-conjuncts`), with every variable a
  quantifier inside them binds numbered past the rule's own, so exceptions differing only in a
  binder's name are one meta-sentex.  Each conjunct is numbered alone first, its conjunctions
  ordered as a rule's `unknown` antecedent's are (`sort-query-conjunctions`,
  `naf-numberings`), then once more across the sorted conjuncts.  A deferred literal keeps its
  written place among the deferred literals of its conjunction, after the generators."
  [conjuncts rule-vars]
  (let [base   {:n (count rule-vars) :m (zipmap rule-vars rule-vars) :vm {}}
        alone  (fn [c] (reduce #(if (neg? (cmp-term %2 %1)) %2 %1)
                               (map first (naf-numberings base
                                                          (sort-query-conjunctions c deferred-literal?)
                                                          (delay #{}) deferred-literal?))))
        number (fn [n c] (number-form (assoc base :n n) c))]
    (first (reduce (fn [[acc n] c] (let [[r st] (number n c)] [(conj acc r) (:n st)]))
                   [[] (:n base)]
                   (sort-conjuncts (map alone conjuncts))))))

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

  Only the generator literals are reordered.  Two kinds are held back in the author's relative
  order: deferred (evaluable) literals, and the recursive literal of a recursive rule, whose
  reordering could make it left-recursive (`vaelii.impl.resolution`).  Generators are sorted
  with the variable-blind comparator; ties (a same-predicate self-join) are resolved by
  searching the orderings of the tie group (`minimal-orders`, exact, no cutoff) and keeping
  the one whose canonically numbered form is smallest on the whole rule (`cmp-render`:
  antecedents, then consequent).  A held-back `unknown` literal's conjunctions are ordered by
  the same search (`naf-numberings`).  An `exceptWhen` is a separate meta-sentex aligned to
  this rule's `varmap` at assert (`vaelii.core`)."
  [antes conseq marks]
  (let [norm       #(normalize-literal % marks)
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
        tail-vars  (delay (suffix-vars (mapv vector defs) (set (form-vars conseq0))))
        render     (fn [cand]
                     (for [{:keys [order st]} (number-each [cand] defs naf-numberings
                                                           #(delay (nth @tail-vars %)))
                           :let [[conseq' st'] (number-form st conseq0)]]
                       [order conseq' (:vm st')]))
        candidates (minimal-orders empty-numbering
                                   (tie-groups (vec (sort cmp-blind gens)))
                                   (into #{} (mapcat form-vars) (conj defs conseq0))
                                   (into #{} (mapcat form-vars) defs)
                                   [conseq0]
                                   naf-numberings)]
    (reduce (fn [best r]
              (if (or (nil? best) (neg? (cmp-render r best))) r best))
            nil (mapcat render candidates))))

;; ---- definitional collection relations -----------------------------------
;; `defnNecessary` / `defnSufficient` / `defnIff` tie a collection's membership to a
;; defining condition on the member, expanded into ordinary forward rules at assert
;; (docs/defns.md).  A `defn*` fact is stored like any other — so it retracts and
;; belief-follows — and carries the member variable `?x` inside its condition argument,
;; which is why it is exempted from the ground check the way a schematic equation is.

(def defn-member-var
  "The distinguished variable a `defn*` sentence names the member by.  `(defnNecessary
  Coll <cond>)` reads `<cond>` as a condition on `?x` and expands to a rule relating
  `(Coll ?x)` to it.  One fixed spelling, so the member stays identifiable after
  canonicalization renames every other variable in the condition."
  '?x)

(def defn-predicates
  "The three definitional collection relations, each expanded into forward rules at
  assert (docs/defns.md).  A syntactic set, read where a `defn*` sentence must be
  recognized: exempted from the ground check (its condition carries `?x`), given a
  well-formedness arm, and materialized into companion rules."
  '#{defnNecessary defnSufficient defnIff})

(defn defn-sentence?
  "Is `sentence` one of the definitional collection relations — `defnNecessary`,
  `defnSufficient` or `defnIff`?  Read off the functor, so it recognizes the fact a
  `defn*` assertion stores rather than any rule it expands into."
  [sentence]
  (and (sequential? sentence) (contains? defn-predicates (first sentence))))

(defn- defn-condition-antecedents
  "A `defn*` condition read as an antecedent list — a leading `and` flattened, anything
  else the single antecedent — so a conjunctive sufficient condition becomes a
  conjunctive rule body."
  [cond]
  (if (and (sequential? cond) (= and-functor (first cond)))
    (vec (rest cond))
    [cond]))

(defn defn-companion-rules
  "The forward rule sentence(s) a `defn*` sentence expands into, each relating `(Coll ?x)` to
  the condition on the member `?x`:

      (defnNecessary  Coll C) -> [(implies (Coll ?x) C)]   ; member => condition
      (defnSufficient Coll C) -> [(implies C (Coll ?x))]   ; condition => member
      (defnIff        Coll C) -> both

  Built from the sentence as written and canonicalized when stored; a conjunctive necessary
  condition splits into one rule per conjunct.  A sufficient condition with no generator
  conjunct naming `?x` expands to no rule (`check-naf-closed` would refuse it), and
  `DefnSufficientProver` answers membership."
  [[pred coll cond]]
  (let [member     (list coll defn-member-var)
        ;; A companion rule materializes membership (or the condition) forward, so it is
        ;; wrapped set/forwardRule (forward + backward) rather than left bare, which the
        ;; backward default would otherwise make backward-only.
        fwd        (fn [r] (list 'set/forwardRule r))
        necessary  (fwd (rule-sentence [member] cond))
        antes      (defn-condition-antecedents cond)
        sufficient (when (some #(and (not (or (unknown? %) (forall? %) (deferred-literal? %)))
                                     (some-symbol? #{defn-member-var} %))
                               antes)
                     (fwd (rule-sentence antes member)))]
    (case pred
      defnNecessary  [necessary]
      defnSufficient (if sufficient [sufficient] [])
      defnIff        (if sufficient [necessary sufficient] [necessary]))))

(defn defn-condition-problems
  "Why the `defn*` sentence `s` is not well-formed, as problem strings (empty if OK).
  The condition must mention the member variable `?x`: a condition that does not name
  the member says nothing about membership, and would expand to a rule that concludes it
  vacuously (necessary) or is not range-restricted (sufficient)."
  [[pred _coll cond :as s]]
  (cond-> []
    (not= 3 (count s))
    (conj (str pred " takes a collection and a condition on the member " defn-member-var))

    (and (= 3 (count s)) (not (some-symbol? #(= defn-member-var %) cond)))
    (conj (str pred " states a condition on the member " defn-member-var ", but "
               (pr-str cond) " does not mention " defn-member-var))))

;; ---- construction --------------------------------------------------------

(defn- constructed-sentex
  "The ordinary sentex construction: peel the direction / default / assumption / (surface)
  exceptWhen wrappers, then canonicalize a rule or a fact.  Split out of `sentex` so the
  exceptWhen meta-sentex short-circuit there reads cleanly."
  [sentence context marks]
  (let [[dir def? _exc assum con inner0] (peel-rule-wrapper sentence)
        ctx              (intern-sym context)
        inner            (canon inner0)
        [polarity body]  (peel-not inner)
        rule?            (implies? body)]
    (if rule?
      (let [body       (desugar-forall-rule body)     ; forall is nested NAF, at the entry point
            antes0     (rule-antecedents body)
            conseq-raw (rule-consequent body)
            ;; a head existential `(exists ?y C)` stores as its inner `C` (docs/skolem.md)
            conseq0   (if (head-exists? conseq-raw) (head-exists-body conseq-raw) conseq-raw)]
        ;; A surface `exceptWhen` wrapper (`_exc`) is stripped and dropped here: the
        ;; exception is not part of the rule and cannot be represented on the record.  The
        ;; assert layer splits it off first and stores it as a meta-sentex (`vaelii.core`),
        ;; so a pure construction of a wrapped rule stores the bare rule alone.
        ;; `check-naf-closed` reads the surface antecedents, after the `forall` desugar.
        (check-naf-closed antes0 conseq0 nil)
        (let [antes1 (desugar-there-exists antes0)      ; standalone thereExists -> body
              [antes conseq varmap]
              (canonicalize-rule antes1 conseq0 marks)
              ;; A bare implies is backward by default.  Forward chaining materializes a
              ;; conclusion per match, which is intractable on a large KB, so it is opt-in
              ;; (`set/forwardRule`).  A generator is the one exception: it generates a rule by
              ;; firing forward and no backward goal asks for a rule, so a bare generator
              ;; stays forward.  `set/forwardRule` runs a rule forward *and* backward, so
              ;; wrapping a rule never removes a backward use it had — which is what lets a
              ;; rule move to forward by adding the wrapper alone.
              [engines effect]
              (rule-slots dir assum con (solve-wrapped? sentence)
                          (implies? (peek (peel-rule-wrapper conseq0))))]
          ;; A rule record holds its antecedent and consequent and no sign, so a negated
          ;; rule has no representation.  `connective-problems` refuses one at `assert`;
          ;; this refuses it on the paths that construct without asserting (import, a
          ;; canonical-form read).
          (when (= polarity :negative)
            (throw (ex-info (str "a rule cannot be negated: " (pr-str sentence)
                                 " — a rule record holds no sign; negate its consequent"
                                 " instead")
                            {:type :not-well-formed :sentence sentence})))
          (sentex-types/->RuleSentex ctx nil antes conseq nil varmap engines def? effect)))
      (let [b      (normalize-literal body marks)
            stored (if (= polarity :negative) (list not-functor b) b)]
        ;; a wrapper on a non-rule is meaningless; it is stripped and ignored
        (sentex-types/->LiteralSentex stored ctx nil nil)))))

(defn sentex
  "Construct a sentex, a `LiteralSentex` or a `RuleSentex`, canonicalizing the structural
  connectives into the record and the sentence into canonical form (see the namespace
  docstring).  Context defaults to 'default; id defaults to nil until the record store assigns
  a handle.

  `opts` may carry the canonicalization reads (`normalize-literal`): `:symmetric?`,
  `:groups-of`, `:opaque?`, `:mention-at?`, `(fn [functor position])`, and the term marks
  `:associative?`, `:idempotent?`, `:meet-order` and `:distinct-from`.  The sorts apply to
  the literal and every compound below it, the term marks to the compounds below it
  (`canonical-term`).  Without them no predicate commutes anything."
  ([sentence] (sentex sentence 'default))
  ([sentence context] (sentex sentence context nil))
  ([sentence context {:keys [symmetric? groups-of opaque? mention-at? associative? idempotent?
                             meet-order distinct-from]
                      :or   {symmetric?    (constantly false) groups-of   (constantly nil)
                             opaque?       (constantly false) mention-at? (constantly false)
                             associative?  (constantly false) idempotent? (constantly false)
                             meet-order    (constantly nil)   distinct-from (constantly nil)}
                      :as   _opts}]
   ;; A `(exceptWhen <query> (sentexHandle H))` meta-sentex is stored **verbatim** as a
   ;; Literal — `peel-rule-wrapper` would otherwise strip the exceptWhen and drop the
   ;; query, since it cannot tell the stored meta form from the surface wrapper.  This is
   ;; the one point that can: the wrapper's second argument is a rule, the meta's is a
   ;; handle.  Its query holds the rule's canonical variables, so it is a non-ground
   ;; Literal — exempt from the ground-fact check by the assert layer.
   (if (exceptWhen-meta? sentence)
     (sentex-types/->LiteralSentex (canon sentence) (intern-sym context) nil nil)
     (constructed-sentex sentence context
                         {:symmetric? symmetric? :groups-of groups-of :opaque? opaque?
                          :mention-at? mention-at? :associative? associative? :idempotent? idempotent?
                          :meet-order meet-order :distinct-from distinct-from}))))

(defn body
  "The positive atomic form a sentex asserts (a fact's sentence without its `not`);
  nil for a rule."
  [{:keys [sentence antecedent]}]
  (when-not (some? antecedent)
    (if (negation? sentence) (second sentence) sentence)))

(defn positive-body
  "The double-negation-eliminated positive body of a sentence, or nil when the
  sentence is genuinely negative.  Constraint checks use this rather than the full
  canonical form: they must see the predicate and argument order the *author* wrote,
  not a folded sibling (`greaterThan` ⇒ `lessThan`) or sorted symmetric arguments,
  or an `arg` would be enforced against the wrong position."
  [sentence]
  (let [[polarity body] (peel-not (canon sentence))]
    (when (= :positive polarity) body)))

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

(defn- ist-rule-problem
  "The refusal message an `(ist Ctx S)` in the rule position `role` (`:antecedent`,
  `:exception` or `:consequent`) carries
  (docs/contexts.md#ist-find-or-create-in-a-context)."
  [role]
  (if (= :consequent role)
    (str "an (ist Ctx S) consequent places the conclusion in Ctx whether or not Ctx sees"
         " the rule and the facts it rests on — conclude S plainly, and make it visible"
         " with (decontextualized_predicate P) or a genlCx edge")
    (str "an (ist Ctx S) " (clojure.core/name role) " matches no stored sentex, so the"
         " rule never consults Ctx — make S visible with (decontextualized_predicate P)"
         " or a genlCx edge, and write S plainly")))

(def ^:private negated-query-heads
  "The query operators a condition may not negate (`connective-problems`)."
  #{unknown-functor there-exists-functor forall-functor})

(defn connective-problems
  "Structural problems with `sentence`'s connective frames, as strings (empty if OK), read by
  `check` and thrown by `assert` under `:not-well-formed` before anything is stored:

  - a structural connective at an arity it does not have;
  - a rule or exception literal that is not itself a sentence; a bare variable is a term, and
    a derived sentence whose predicate a firing binds is written `(?pred . ?args)`;
  - a head existential outside consequent position;
  - an `(ist Ctx S)` in any rule position (`ist-rule-problem`);
  - a nested `implies` anywhere but a rule's consequent, where it is a generator
    (docs/generators.md), checked at each level in the ordinary rule roles;
  - a negated rule: `not` over an `implies`, bare or wrapped;
  - a top-level `and`, or a top-level `or`, or a `not` over one (docs/canonicalization.md);
  - a `not` over `unknown`, `thereExists` or `forall` in an antecedent or an exception, at any
    depth (docs/naf.md);
  - a combination of `set/*` wrappers the record cannot hold (`wrapper-stack-problems`)."
  [sentence]
  (letfn
   [;; the one sentence a wrapper or a `not` takes.  Below the top level a bare symbol
    ;; is caught by `walk1`'s literal arm; at the top level that arm defers to the
    ;; sentence-shape check, which reads the outermost form only, so the operand is
    ;; judged here
    (operand [role h x stacked?]
      (if (and (= :sentence role) (not (sequential? x)))
        [(str (pr-str h) " takes a sentence, got " (pr-str x))]
        (walk role x stacked?)))
    (walk
      ([role form] (walk role form false))
      ;; `stacked?` is true inside a wrapper stack, so the stack's combination is judged
      ;; once, at its outermost wrapper (`wrapper-stack-problems`)
      ([role form stacked?]
       (let [ps (walk1 role form)]
         (if (or stacked? (empty? (wrapper-stack form)))
           ps
           (into (wrapper-stack-problems form) ps)))))
    (walk1 [role form]
      (cond
        (not (sequential? form))
        (if (= :sentence role)
          []                                       ; top-level shape has its own check
          [(str ({:antecedent "an antecedent" :exception "an exception"} role "a consequent")
                " literal must be a sentence, got " (pr-str form)
                (when (variable? form)
                  (str " — a variable is a term, not a formula"
                       (when (= :consequent role)
                         (str "; write the consequent as (?pred . ?args), bound in the"
                              " antecedent")))))])
        (empty? form) ["an empty form is not a sentence"]
        :else
        (let [h (first form) n (count form)]
          (cond
            (variable? h)                 []       ; `(?p ?x)` names no connective
            (do-form? form)               []
            (= sentex-handle-functor h)   []
            ;; a constraint wrapper takes one rule, optionally after a leading integer
            ;; priority level — `(set/softConstraint 2 (implies …))` — which
            ;; `rules/normalize-soft-priority` moves onto the consequent marker before store
            (constraint-rule-wrappers h)
            (cond
              (= 2 n)                                (operand role h (second form) true)
              (and (= 3 n) (integer? (second form))) (operand role h (nth form 2) true)
              :else [(str (pr-str h) " wraps one rule (optionally after a priority level), got arity "
                          (dec n))])
            (or (= h default-rule-wrapper) (= h assumption-rule-wrapper) (= h solve-rule-wrapper)
                (contains? rule-direction-wrappers h))
            (if (= 2 n)
              (operand role h (second form) true)
              [(str (pr-str h) " wraps one rule, got arity " (dec n))])
            (= h except-wrapper)
            (if (= 3 n)
              (into (vec (mapcat #(walk :exception %)
                                 (exception-conjuncts (second form))))
                    (operand role h (nth form 2) true))
              [(str "exceptWhen takes a query and a rule, got arity " (dec n))])
            (= h not-functor)
            (cond
              (not= 2 n)
              [(str "not takes one sentence, got arity " (dec n))]
              (implies? (peek (peel-rule-wrapper (second form))))
              ["a rule cannot be negated; retract it, or state the exception the negation means"]
              ;; below the top level `rules/disjunction-problems` names the rule rewrite
              (and (= :sentence role) (disjunction? (second form)))
              [(str "(not (or A B)) is \"neither A nor B\", a conjunction of negations"
                    " rather than one assertable sentence; assert each negation as its own"
                    " fact")]
              ;; a top-level one is a fact, which `special/wff-problems` refuses
              (and (contains? #{:antecedent :exception} role)
                   (sequential? (second form))
                   (contains? negated-query-heads (first (second form))))
              [(str "(not (" (first (second form)) " …)) negates a query, and no prover"
                    " answers it, so the condition never holds; write (unknown (forall …))"
                    " or (unknown (thereExists …)) for the closed-world reading, and S for"
                    " (not (unknown S))")]
              :else (operand role h (second form) false))
            (= h ist-functor)
            (cond
              (contains? #{:antecedent :exception :consequent} role) [(ist-rule-problem role)]
              (= 3 n)        (walk role (nth form 2))
              (= :sentence role) []  ; the top-level ist arity has its own `:shape` contract
              :else [(str "ist takes a context and a sentence, got arity " (dec n))])
            (= h and-functor)
            (if (= :sentence role)
              ["a conjunction is not one assertable sentence; assert its conjuncts"]
              (vec (mapcat #(walk role %) (rest form))))
            (and (= h or-functor) (= :sentence role))
            [(str "a disjunction is not one assertable sentence: nothing decides which"
                  " alternative holds, and belief is a label on a sentex rather than on a"
                  " set of them.  As a rule antecedent an or expands to one rule per"
                  " alternative; as a conclusion, offer the alternatives to a solve with"
                  " set/assumptionRule (docs/solving.md)")]
            (= h rule-functor)
            (cond
              (not= 3 n)
              [(str "implies takes antecedents and one consequent, got arity " (dec n))]
              ;; A rule **in consequent position** is a generator's head: the rule its
              ;; firing generates (docs/generators.md).  Its own parts are checked in
              ;; the ordinary rule roles, so every arm below — `ist`, a head
              ;; existential, a negated antecedent — holds of the generated rule exactly
              ;; as it holds of a written one, at whatever depth it sits.
              ;;
              ;; The recursion is the whole of the nesting rule: a generated rule that
              ;; generates a rule is read here exactly as the one above it was, and the
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
            ;; bare literal is, and for the sharper reason (`ist-rule-problem`).  Only
            ;; where `unknown` means anything: it is an antecedent/exception construct,
            ;; and a top-level one is not a sentence this check is owed an opinion on.
            (and (unknown? form) (not= :sentence role)) (walk role (second form))
            (there-exists? form) (walk role (nth form 2))
            (aggregate? form)    (walk role (aggregate-body form))
            :else []))))]
    (walk :sentence sentence)))

(defn connective-problem
  "`connective-problems` as one `:not-well-formed` problem map, or nil.  `assert` and
  `check` read it right after the sentence shape, and an import reads it over each frame,
  so a malformed connective frame is refused before it can store as an opaque fact or a
  rule that answers wrongly."
  [sentence]
  (when-let [ps (seq (connective-problems sentence))]
    {:type :not-well-formed :sentence sentence
     :message (str "not well-formed: " (str/join "; " ps))}))

(defn rename-vars
  "`form` with every variable `m` names replaced by the name it maps to, in one pass: each
  position is rewritten at most once.  Unmapped terms are left alone and a vector stays a
  vector.  A renaming is a permutation and has cycles, so `{?var0 ?var1, ?var1 ?var0}` over
  `(P ?var0 ?var1)` gives `(P ?var1 ?var0)`, where `res/substitute` would chase
  `?var0 → ?var1 → ?var0`.  It carries a form between two canonical namings: the map
  `canonical-conjunction` returns, a rule's `:varmap`, a cache's rename-back."
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

(defn authored-sentence
  "A stored sentex's sentence with the author's variable names restored through its own
  `:varmap`; a fact carries no varmap and its sentence comes back unchanged.  The one
  spelling of the display form: `vaelii.core/readable-sentence` delegates here, and
  `chain`'s refusal report, `inference`'s proof tree, `io.text`'s writer, `quality`'s
  rule lines and `violations`' dropped-rule entry call it."
  [sx]
  (if-let [vm (:varmap sx)]
    (originalize (sentence-of sx) vm)
    (sentence-of sx)))

(defn canonical-conjunction
  "`[canonical varmap]` for a conjunction: every variable across all of `literals` renumbered
  `?var0 ?var1 …` by first occurrence under one shared numbering, and the map from each
  canonical name back to the name it replaced.  Two conjunctions differing only in variable
  names become the same value, so a search can recognize a repeat.  `varmap` carries a
  solution back to the caller's names, applied with `rename-vars` in one pass because the map
  can be a permutation.

  `start` numbers from `?var<start>`, which renames a form clear of another whose variables
  are `?var0 … ?var<start-1>`, as unifying a stored rule against a conjunction requires."
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
;; children (recursing for nested arity), with no balanced close-marker.  What the
;; marker buys is that *how many* to skip is read rather than scanned for; the skip
;; itself still fans over the node's children, which is the frontier cost the secondary
;; roots exist to keep a query off.
;;
;; The marker is a 2-vector `[::subterm k]`.  Nippy keeps keywords, ints, symbols and
;; strings as distinct types (see the storage note), and after linearization no trie
;; token is ever a vector — arguments are symbols/numbers/strings or (nested) lists,
;; and the connective frame is peeled — so a vector token is unambiguously a marker.
;; A `:false` / `:rule` key keeps its literals whole (a list token, never a vector),
;; and `lookup` treats such a list as a single opaque form, so those keys are
;; unchanged: only positive-fact keys linearize.

;; The tag and the three marker functions are `vaelii.impl.types.sentex`, which the
;; columnar trie calls.
(def subterm-mark  "An arity marker for a `k`-element subterm." sentex-types/subterm-mark)
(def subterm-mark? "Is `x` an arity marker?" sentex-types/subterm-mark?)
(def subterm-arity "The element count an arity marker carries." sentex-types/subterm-arity)

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
  leading marker, so the `[pred …]` prefix and the predicate extent's node `[pred]` stay
  the trie's first level), then each argument linearized.  Deterministic and
  compound-blind, so it composes with α-rename and dedup unchanged — an atom body
  degenerates to `[body]`."
  [body]
  (if (and (sequential? body) (seq body))
    (cons (first body) (mapcat linearize (rest body)))
    [body]))

;; ---- indexing key -------------------------------------------------------

(defn- key-tokens
  "The trie tokens for a sentex, with the `implies` / `and` rule frame canonicalized out and
  variables α-renamed.  A rule is keyed `[:rule <antecedents> <consequent> <choice>
  <constraint>]` (a negative literal inside keeps its `not`); a negative fact `[:false
  <body>]`; a positive fact is its body linearized, the functor then each argument in
  preorder, so a nested compound is a run of trie levels.

  The two trailing slots spell the rule's `:effect` (`true` in the first for a choice rule,
  `:hard` / `:soft` in the second for a constraint rule) and are present, as nil, on every
  rule, so every rule keys at one depth and a wildcard context slot cannot descend into child
  tokens.  An `exceptWhen` is a separate meta-sentex and is not keyed here.

  Rules and `:false` bodies keep their literals whole.  A negative key therefore matches only
  exactly, and `res/candidate-handles` routes an open negative to the secondary roots, which
  span both polarities."
  [{:keys [sentence antecedent effect] :as sx}]
  (if (some? antecedent)
    ;; the rule's whole form, renamed as one, so the antecedents and the consequent
    ;; share one numbering — the key the layout on disk holds.  The two trailing slots
    ;; are the `:effect`'s spelling in that layout: `true` in the first for a choice, the
    ;; constraint class in the second, nil and nil for a `:derive` rule
    (let [a (alpha-rename (sentence-of sx))]
      [:rule (vec (rule-antecedents a)) (rule-consequent a)
       (when (= :choose effect) true) (effect-constraint effect)])
    (let [a (alpha-rename sentence)]
      (cond
        ;; `:false` is the index's own path token for a negative literal: the token
        ;; alphabet is machine vocabulary and the layout is on disk.
        (negation? sentence) [:false (second a)]
        (sequential? a)    (vec (key-stream a))
        :else              [a]))))

(defn path
  "The full trie path for a sentex: its (connective-free, α-renamed, structurally
  linearized) key tokens with the context appended as the final level."
  [sentex]
  (conj (key-tokens sentex) (:context sentex)))

(defn ground?
  "True when the sentence contains no pattern variables (anywhere, nested).  A plain tree
  search: a variable inside a `(Quote …)` or under a quantifier counts.  `closed?` is the
  test for a sentence with no free variable."
  [sx]
  (not (some-symbol? variable? (sentence-of sx))))

(defn unquoted-free-vars
  "The variables of `form` free in it: every variable occurrence that no enclosing
  `forall`, `thereExists` or head `exists` binds and no `(Quote …)` holds.  A `Quasiquote`
  is not opaque, since its variables are meant to be bound from outside."
  [form]
  (cond
    (quote-form? form)   #{}
    (or (there-exists? form) (forall? form) (head-exists? form))
    (into #{} (remove (quantified-vars form)) (unquoted-free-vars (nth form 2)))
    (variable? form)     #{form}
    (sequential? form)   (into #{} (mapcat unquoted-free-vars) form)
    :else                #{}))

(defn closed?
  "True when the sentence has no free variable: every variable occurrence is bound by an
  enclosing quantifier or sits inside a `(Quote …)`, the quoted form being syntax the
  sentence mentions.  A `ground?` sentence answers at once.  This is the test for \"is
  this sentence closed\"; `ground?` is the test for \"does it hold any variable\"."
  [sx]
  (or (ground? sx)
      (empty? (unquoted-free-vars (sentence-of sx)))))

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
  `(unary_predicate not)`) is data, not a connective, and is left intact."
  [form]
  (if (and (sequential? form) (seq form))
    (case (first form)
      not           (literals (second form))
      (and implies) (mapcat literals (rest form))
      [form])
    [form]))

(defn- term-children
  "The subterms of the compound `form` the term index descends into: all of them, less
  the head of a compound `not` / `and` / `implies` heads, as in a rule quoted in an
  argument (a generator's consequent)."
  [form]
  (cond-> form (contains? '#{not and implies} (first form)) rest))

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
    (sequential? t) (not (some-symbol? variable? t))
    :else           false))

;; ---- which compounds earn a key: a floor and a ceiling ------------------
;; Both bound the same thing — which compounds are *stored* as keys — and neither touches
;; an atom: a symbol is keyed wherever it sits, at every depth, under every setting.  So
;; neither bound makes anything unfindable.  What a compound outside them costs is a read
;; rather than a key: `kb/find-sentexes` narrows on the atoms it contains and verifies the
;; candidates against their records (`probe-atoms` / `mentions?`, below).

(def ^:dynamic *min-indexed-depth*
  "How deep inside a content literal a ground **compound** must sit to earn its own
  inverted-index key: `0` is the literal itself, `1` a subterm of it.

  The default 1 drops each literal's own whole-compound key, which mints one key holding one
  handle per record and makes the token dictionary fact-scaled: 12,054 of 12,565 distinct
  tokens in a 12,070-record corpus, 1,724 of 2,077 in the shipped starter.  The keys kept at
  depth 1 are the nesting a probe is for: `(sentexHandle H)` inside an `exceptWhen` meta and
  the sentence inside an `(ist Ctx S)`.  `2` and up also drop that wrapped sentence.  `0` keys
  every compound.

  It is read at write time.  Moving it over a populated store leaves written keys, which are
  stale and not wrong, and `reindex` applies a new setting."
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
  every depth (`term-children`), and each compound sitting at `floor` or deeper (`d` is
  `form`'s own depth, 0 for the literal).  A compound shallower than the floor is still
  *descended into* — the floor drops its key, never its contents — so the atoms are the
  same set at every setting."
  [form ^long d ^long floor]
  (if (sequential? form)
    (let [inner (mapcat #(keyed-subterms % (inc d) floor) (term-children form))]
      (if (>= d floor) (cons form inner) inner))
    (list form)))

(defn index-terms
  "The distinct terms that make a sentex findable: the atoms of its connective-free
  content at every depth, plus each ground compound between `*min-indexed-depth*` and
  `max-indexed-compound`.  The dot marker of a rest pattern is syntax and names no term.
  The sentex's context is added separately by the index."
  [sentex]
  (let [floor (long *min-indexed-depth*)]
    (into #{} (comp (mapcat #(keyed-subterms % 0 floor))
                    (filter indexable-term?)
                    (remove #{dot-marker})
                    (remove oversized-compound?))
          (content-forms sentex))))

(defn probe-atoms
  "The keys a **compound** probe narrows by: the indexable atoms it contains, read as
  `keyed-subterms` reads them (`term-children`).  Every sentex holding the compound holds
  all of them — atoms are keyed at every depth under every bound — so their intersection
  is a superset of the answer, whatever key the compound itself does or does not earn.  A
  compound holding no indexable atom — no symbol anywhere in it — has nothing to narrow by
  and probes by its own key: at the default floor it can only occur nested, which is where
  it has one."
  [term]
  (let [atoms (fn atoms [t] (if (sequential? t) (mapcat atoms (term-children t)) [t]))
        as    (into [] (filter indexable-term?) (atoms term))]
    (if (seq as) as [term])))

(defn mentions?
  "Does `sentex`'s connective-free content hold `term` as a subterm?  The question the
  term index answers wherever it has a key, asked of the record instead — the verify half
  of a compound probe, which turns `probe-atoms`' superset into the exact answer."
  [sentex term]
  (boolean (some (fn [form] (some #(= % term) (subterms form)))
                 (content-forms sentex))))

(caches/register-derived
 {:id :K1 :label "Symbol pool" :cache :symbol-pool :kind :cache :keyed-by :value :reads []
  :holds-content? false
  :retired-by {} :computed :read :imaged? false :var #'symbol-pool-generations
  :value (fn [_] @symbol-pool-generations)
  :note "content-keyed: two generations, the older dropped at half the bound"})
