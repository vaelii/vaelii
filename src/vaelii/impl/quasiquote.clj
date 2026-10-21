;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.quasiquote
  "Quasiquotation — the metalinguistic constructor (mention-opacity: docs/argtypes.md).

  `(Quasiquote T)` builds the syntactic term `T` with each `(Unquote v)` hole replaced by
  `v`, and names the result *as syntax* — a mention.  `(Quasiquote (isa (Unquote ?x) Dog))`
  fired with `?x`=Fido constructs the term for `(isa Fido Dog)`.

  The model is **skolemization**, not the `evaluate` prover: a `Quasiquote` is a
  term-constructor sitting in argument position (`(believes Tom (Quasiquote …))`), built
  deterministically from a firing's bindings and reified when the conclusion is placed.  Reduction of a
  ground `(Quasiquote T)` strips its `Unquote` holes to the expression `E`, then reifies
  `(Quote E)` — `Quote` being a reifiable **quoting** function, so `E` reifies to an opaque
  `nat/` constant that mention-opacity holds apart from its referents' merges.  Determinism
  is content-addressed for free: `E` *is* the content, so `nat/reify-or-mint-nat` dedups two
  firings on one binding to one constant (no rule digest / frontier is needed, unlike a
  skolem witness, which is anonymous).

  `Quasiquote` is an `unreifiable_function`, so an *open* template — the one that lives in a
  rule consequent until the antecedent binds its `Unquote` holes — stays structural and is
  never minted; range restriction (`rules/check-range-restricted`) already refuses a hole no
  antecedent binds, so an open template never reaches storage.  `Quote` and `Quasiquote` are
  the engine's quoting functions (`sx/quoting-functors`), fixed rather than declared, so
  while a template waits in the rule its `Unquote`-marked spellings are held opaque to an
  identity merge exactly as a `Quote` payload is, in every KB and from the first assert.

  The reducer is turned on by declaration, like `reifiable_function` turns the reify pass
  on: a KB that has not declared `(unreifiable_function Quasiquote)` pays one taxonomy-prop
  read per firing/assert and the reducer is a no-op.  Reduction mints through the reify
  pass, so `ensure-quasiquote-functions` (or the marks it asserts) precedes the
  constructions it reduces."
  (:require [vaelii.impl.kb :as kb]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wiring :as wiring]))

(def quasiquote-function
  "The reserved template-constructor functor, keyed on by name like `SkolemFn` — one of the
  engine's quoting functions (`sx/quoting-functors`)."
  sx/quasiquote-functor)

(def unquote-marker
  "The reserved hole marker: `(Unquote v)` inside a template splices `v` into the
  constructed expression.  Meaningful only inside a `Quasiquote` body."
  'Unquote)

(def quote-function
  "The reifiable quoting function a reduced template mentions its result through — one of
  the engine's quoting functions (`sx/quoting-functors`)."
  sx/quote-functor)

(defn any-quasiquote?
  "Gate: is quasiquotation enabled — `(unreifiable_function Quasiquote)` declared?  False ⇒
  the reducer short-circuits, one prop read.  Mirrors `nat/any-reifiable-functions?`.

  The mark is read unscoped: the gate asks whether the KB stores it."
  [kb]
  (tax/has-prop? (reasoning/taxonomy kb) :unreifiable quasiquote-function))

(defn ensure-quasiquote-functions
  "Enable quasiquotation as a unit — declare the two marks it needs, each only if absent:
  `Quote` reifiable (the constructed expression reifies to a mention constant) and
  `Quasiquote` unreifiable (an open template stays structural).  Both are quoting functions
  without any declaration (`sx/quoting-functors`).  The last mark,
  `(unreifiable_function Quasiquote)`, is the gate `any-quasiquote?` reads, so this call is
  what turns the reducer on.  Idempotent, asserted without chaining or settling since it is
  pure metadata — the shape `skolem/ensure-skolem-function` uses.

  The marks are read unscoped: the question is whether the KB stores each one."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (doseq [s (cond-> []
                (not (nat/reifiable-function? kb quote-function))
                (conj (list 'reifiable_function quote-function))
                (not (tax/has-prop? tax :unreifiable quasiquote-function))
                (conj (list 'unreifiable_function quasiquote-function)))]
      (wiring/assert-sentence kb s nat/universal-context {:strength :monotonic :chain? false}))))

(defn- unquote-form? [x]
  (and (seq? x) (= unquote-marker (first x)) (= 2 (count x))))

(defn quasiquote-form? [x]
  (and (seq? x) (= quasiquote-function (first x)) (= 2 (count x))))

(defn- strip-unquotes
  "The template body `t` with each `(Unquote v)` replaced by `v` — the constructed
  expression.  A `Quasiquote` nested inside is its own mention level and is left **whole**,
  its `Unquote`s untouched, so it stays literal syntax in the constructed expression (and
  `reduce-term` holds it opaque there too — the two must agree, or a construction stored one
  way is queried another)."
  [t]
  (cond
    (unquote-form? t)    (second t)
    (quasiquote-form? t) t
    (vector? t)          (mapv strip-unquotes t)
    (seq? t)             (apply list (map strip-unquotes t))
    :else                t))

(defn- reduce-term
  "Every **ground** `(Quasiquote T)` subterm of `term` replaced by `(reify-fn (Quote E))`,
  `E` its constructed expression.  An open template (a hole still unbound) is left
  untouched — in a rule consequent it reduces at firing, once substitution grounds it; a
  direct open assert is a non-ground fact `wff` already refuses."
  [kb term reify-fn]
  (cond
    (and (quasiquote-form? term) (sx/ground-term? term))
    (reify-fn (list quote-function (strip-unquotes (second term))))
    ;; a mention is opaque — a quoting function's application (`Quote`, or an open/nested
    ;; `Quasiquote`) or a quoting-predicate payload (`natFormula` / `rewriteOf`, the reified
    ;; NAT's own bookkeeping): a `Quasiquote` nested inside is literal syntax, not reduced
    ;; here.  Without this the `(natFormula K E)` re-assert `mint-nat!` makes would re-run
    ;; over `E` and reduce a nested construction the write already fixed, leaving it stored
    ;; one way and queried (top level only) another.
    (and (seq? term)
         (or (contains? nat/nat-quoting-predicates (first term))
             (sx/quoting-functor? (first term))))
    term
    (vector? term) (mapv #(reduce-term kb % reify-fn) term)
    (seq? term)    (apply list (map #(reduce-term kb % reify-fn) term))
    :else          term))

(defn maybe-reduce
  "Strip ground `Quasiquote`s to their `(Quote E)` mention form on the write, derivation and
  read paths, and stop — the reify pass beside it (`maybe-reify-nats` on write and
  `chain/reify-conclusion` on a fired conclusion, both minting; `maybe-reify-for-read` on
  read, deduping) reifies `(Quote E)`, so the spellings of one construction meet at one
  constant.  Structural: mints nothing itself.  Gated — a no-op unless quasiquotation is
  declared."
  [kb sentence]
  (if (any-quasiquote? kb)
    (reduce-term kb sentence identity)
    sentence))

(defn prepare-goal-for-read
  "Bring a `prove` / `query` / `ask` goal (a formula, or a vector of them = a conjunction)
  into the form the stored content is in, so a lookup can meet it: **reify** ground
  NATs to their existing constants, then **rewrite** terms to their equality-class
  representatives and schematic normal forms (`kb/rewrite-goal`).

  This is the parity every read path holds to, and the backward chainers need it as
  much as the rest: without the rewrite step a goal naming a merged spelling — or one
  an oriented equation would normalize — is answered by `sentexes-matching`/`ask` but
  silently missed by `prove`/`query`, and the same knowledge answers path-dependently.
  It is the **top** goal that is normalized, exactly as `sentexes-matching`/`ask`
  normalize theirs; stored facts are already in normal form (migration), so subgoals a
  rule expansion generates need no further rewriting — the same reliance `ask` makes.
  `rewrite-goal` exempts
  `different` and a positive equation, whose arguments must stay un-rewritten to read class
  membership (`res/goal-held-as-spelled?`), and the
  congruence walk under it exempts a **mention** — a quoting function's arguments, and the
  proposition a `modal_predicate` attributes to its agent, which is normalized against the
  *agent's* partition where the projection reads it rather than against the asker's
  (docs/belief.md).  Both exemptions hold on the stored side too, so the goal and the
  sentex still meet at one form.

  Rewritten by the merges `context` sees, since that is where the goal is asked.  It lives
  here, beside `maybe-reduce`, because it composes the two read-time reductions
  (`maybe-reduce` and `nat/maybe-reify-for-read`) with the equality rewrite, and both
  `vaelii.core`'s read entry points and `vaelii.impl.predall`'s audit prepare a goal the
  same way through this one function."
  [kb goal context]
  (letfn [(prep [g] (kb/rewrite-goal kb (nat/maybe-reify-for-read kb (maybe-reduce kb g) context) context))]
    (if (vector? goal) (mapv prep goal) (prep goal))))

(defn ask-prepared
  "Answer `goal` through the prover registry in the one context `ctx`, the goal prepared
  as every read prepares it (`prepare-goal-for-read`).  This is `vaelii.core/ask`'s
  per-context step, which `ask` and `ask?` call inside `read-in-context`, and the whole of
  the read the `fluent` and `predall` audits run below `vaelii.core`: they pass a concrete
  context, expand no rule, and the `genlCx` ancestor scoping is applied in the matching
  layer below."
  [kb goal ctx]
  (provers/ask kb (prepare-goal-for-read kb goal ctx) ctx))
