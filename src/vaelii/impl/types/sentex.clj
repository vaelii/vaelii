;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.sentex
  "The two sentex records, as a held namespace (`vaelii.impl.types.prover` states what that
  means).  Every stored sentex is one of these, so a reload that redefined them would
  leave a loaded KB's records unequal to every record built after it.  Building,
  canonicalizing and reading a sentex is `vaelii.impl.sentex`.")

;; Two records, split so a literal sentex does not carry the seven rule-only slots
;; (facts are the 100M+ case).  Both share the scalar core:
;;   context     the context symbol it holds in
;;   id          the integer handle, nil until the record store assigns one
;;   strength    :monotonic | :default | nil    (the assumption strength when the
;;               sentex is asserted as a premise; nil for a purely-derived one)
;;
;; A `LiteralSentex` is a literal — a fact or its negation, a metadata declaration, or a
;; query pattern: one signed predicate application, ground or holding variables.  It adds
;; `sentence` to the core — the canonical, readable form, `(not S)` for a negative
;; literal, which display and matching read — and reading any rule-only key off it
;; returns nil, so `(some? (:antecedent sx))` is the literal-vs-rule discriminant
;; everywhere.
;;
;; The sign is **the sentence's own head**, not a slot: a negative literal's sentence is
;; `(not S)`, and `negative?` reads that.  Which literal a sentex is says nothing about
;; belief — whether the KB *holds* it is `jtms/in?`, which reads a handle.  A negative
;; literal the JTMS believes is a believed denial, and a positive one it does not is a
;; defeated positive; the two axes are independent.
(defrecord LiteralSentex [sentence context id strength])
;;
;; A `RuleSentex` is an implication.  Beyond the core it carries the decomposition the
;; connectives and `set/*` wrappers canonicalize into:
;;   antecedent  [pattern ...]          (the antecedents — the sentence's `and` body)
;;   consequent  pattern                (the consequent)
;;   varmap      {?var0 ?x, …} | nil    (canonical variable -> the author's name)
;;   direction   :forward | :backward | :both | :forward-only | :inert   (from its
;;               set/*Rule wrapper; :backward for a bare implies — the tractable default,
;;               since forward chaining materializes a conclusion per match.  :forward and
;;               :both mean forward + backward (`rules/backward?`), so a set/forwardRule
;;               rule answers backward goals too; :forward-only (set/forwardOnlyRule)
;;               forward-chains but never backward — a tests-only mode the ontology never
;;               uses; a generator stays forward even bare)
;;   defeasible  true | nil             (a set/defaultRule rule: its conclusions are
;;               defeasible and fire from the one agenda like any other rule's;
;;               `settle` decides which of them survive a clash, from recomputed
;;               belief — docs/defenses.md)
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
;;
;; A rule holds **no sentence**.  `antecedent` and `consequent` are the form its readers
;; use — the chainers, the indexers, the checks — and `sentence-of` builds the
;; `(implies …)` form from them for the few that want it whole (the trie key, display).
(defrecord RuleSentex [context id antecedent consequent strength varmap direction
                       defeasible assumption constraint])

;; ---- the term readers the columnar trie calls ----------------------------

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

(def ^:private subterm-tag
  "The head of a structural arity marker — namespaced so it can never be a stored
  token (symbols, numbers, strings, and the `:false` / `:rule` / context slots are
  all type- or value-distinct from `[::subterm k]`)."
  ::subterm)

(defn subterm-mark  [k] [subterm-tag k])
(defn subterm-mark? [x] (and (vector? x) (= subterm-tag (nth x 0 nil))))
(defn subterm-arity [m] (nth m 1))
